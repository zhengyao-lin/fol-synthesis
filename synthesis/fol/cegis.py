from typing import Any, Tuple, Generator, List, Collection

from contextlib import contextmanager

import itertools

from synthesis.smt import smt

from .base import *
from .templates import StructureTemplate
from .utils import FOLUtils
from .prover import NaturalProof, QuantifierKind


class CEGISynthesizer:
    """
    Synthesize formulas that are valid in some class of models
    but not always true in some other class
    """

    def __init__(
        self,
        solver_name: str = "z3",
        check_no_quantifiers: bool = False, # Abort if found a quantified SMT query
        debug: bool = True,
    ):
        self.solver_name = solver_name
        self.check_no_quantifiers = check_no_quantifiers
        self.debug = debug

    @contextmanager
    def solver_push(self, solver: smt.SMTSolver) -> Generator[None, None, None]:
        try:
            solver.push()
            yield
        finally:
            solver.pop()

    def interpret_term_instantiations(
        self,
        solver: smt.SMTSolver,
        language: Language,
        formula: Formula,
        # ground_terms: Mapping[Sort, Collection[Term]],
        structure: Structure,
        depth: int,
    ) -> Language:
        """
        Interpret the term instantiations of a give formula in a given structure

        Returns the extended language
        """
        quants, skolemized = NaturalProof.prenex_normalize(formula.quantify_all_free_variables())
        universal_variables = []

        # skolemize the formula first
        for var, kind in quants:
            if kind == QuantifierKind.UNIVERSAL:
                universal_variables.append(var)
            else:
                # add a skolem function
                fresh_function_name = language.get_fresh_function_name("sk")
                skolem_function_symbol = FunctionSymbol(
                    tuple(universal_var.sort for universal_var in universal_variables),
                    var.sort,
                    fresh_function_name,
                )
                
                # interpret the symbol as a fresh function
                skolem_function_symbol = FunctionSymbol(
                    skolem_function_symbol.input_sorts,
                    skolem_function_symbol.output_sort,
                    skolem_function_symbol.name,
                    structure.get_fresh_function(solver, skolem_function_symbol),
                )

                language = language.expand_with_function(skolem_function_symbol)

                # replace occurrences of the variable with an application of the skolem function
                skolemized = skolemized.substitute({ var: Application(skolem_function_symbol, tuple(universal_variables)) })

        # instantiate the skolemized formula with the given ground terms
        free_vars = tuple(skolemized.get_free_variables())
        combinations: List[Tuple[Term, ...]] = []

        ground_terms = FOLUtils.get_ground_terms_in_language(language, depth)

        for free_var in free_vars:
            combinations.append(tuple(ground_terms.get(free_var.sort, set())))

        for assignment in itertools.product(*combinations):
            assignment_interps = tuple(term.interpret(structure, {}) for term in assignment)
            valuation = dict(zip(free_vars, assignment_interps))
            solver.add_assertion(skolemized.interpret(structure, valuation))

        return language

    def synthesize_for_model_classes(
        self,
        templates: Iterable[Formula],
        trivial_model: StructureTemplate,
        goal_model: StructureTemplate,
    ) -> Generator[Tuple[Formula, Optional[Structure]], None, None]:
        """
        Given a class of models C_1 (described by <trivial_model>)
        and another class of models C_2 (described by <goal_model>)
        Synthesize all formula phi (using each template in <templates> in sequence)
        such that
          - exists M in C_1, not (M |= phi)
          - forall M in C_2, M |= phi

        If the second condition is not true, the counterexample model M is
        added back to the first round as an additional constraint

        e.g. to synthesize formulas true in all bounded finite LFP models but not in all FO model,
        we can take C_1 to be FOProvableStructure and C_2 to be FiniteLFPStructureTemplate

        e.g. to synthesize formulas true in a FO theory T but not in a FO subtheory T'
        we can take C_1 to be FOProvableStructure(T') and C_2 to be FOProvableStructure(T)
        """

        counterexamples: List[Structure] = []
        synthesized_formulas: List[Formula] = []

        new_counterexamples: List[Structure] = []
        new_synthesized_formulas: List[Formula] = []

        with smt.Solver(name=self.solver_name) as gen_solver, \
             smt.Solver(name=self.solver_name) as check_solver: # to check that the synthesized formulas are valid

            gen_solver.add_assertion(trivial_model.get_constraint())
            check_solver.add_assertion(goal_model.get_constraint())

            for template in templates:
                template = template.strip_universal_quantifiers()

                if self.debug:
                    print(f"### synthesizing formulas of the form {template}")

                with self.solver_push(gen_solver):
                    gen_solver.add_assertion(template.get_constraint())

                    # reload all examples synthesized formulas
                    new_counterexamples = counterexamples
                    new_synthesized_formulas = synthesized_formulas

                    # when negated, the (universally quantified) free variables
                    # become existentially quantified, we do skolemization here
                    free_vars = template.get_free_variables()
                    gen_skolem_constants = { # for the fo provable structure
                        v: trivial_model.interpret_sort(v.sort).get_fresh_constant(gen_solver)
                        for v in free_vars
                    }
                    check_skolem_constants = { # for the counterexample
                        v: goal_model.interpret_sort(v.sort).get_fresh_constant(check_solver)
                        for v in free_vars
                    }

                    # not valid in some trivial model
                    gen_solver.add_assertion(smt.Not(template.interpret(trivial_model, gen_skolem_constants)))

                    while True:
                        # add all existing counterexamples
                        for counterexample in new_counterexamples:
                            gen_solver.add_assertion(template.quantify_all_free_variables().interpret(counterexample, {}))
                        new_counterexamples = []

                        # avoid duplicates for all existing formulas
                        for formula in new_synthesized_formulas:
                            # this may lead to quantified SMT queries
                            gen_solver.add_assertion(formula.quantify_all_free_variables().interpret(trivial_model, {}))
                        new_synthesized_formulas = []

                        if self.check_no_quantifiers:
                            for assertion in gen_solver.assertions:
                                assert smt.is_qfree(assertion), f"found quantified formula: {assertion.to_smtlib()}"

                        if not gen_solver.solve():
                            break

                        candidate = template.get_from_smt_model(gen_solver.get_model())
                        if self.debug: print(candidate, "... ", end="", flush=True)

                        # check if the candidate is valid in all goal models
                        with self.solver_push(check_solver):
                            check_solver.add_assertion(smt.Not(candidate.interpret(goal_model, check_skolem_constants)))

                            if check_solver.solve():
                                # found counterexample
                                if self.debug: print("✘")
                                counterexample = goal_model.get_from_smt_model(check_solver.get_model())
                                counterexamples.append(counterexample)
                                new_counterexamples.append(counterexample)
                                yield candidate, counterexample

                            else:
                                # no conuterexample found
                                if self.debug: print("✓")
                                yield candidate, None
                                synthesized_formulas.append(candidate)
                                new_synthesized_formulas.append(candidate)

    def synthesize_for_one_model(
        self,
        templates: Iterable[Formula],
        trivial_model: StructureTemplate,
        goal_model: Structure,
        *_: Any,
        np_indep_language: Language, # Use natural proof to remove dependent formulas
        np_indep_depth: int = 1,
    ) -> Generator[Tuple[Formula, bool], None, None]:
        """
        Similar to synthesize_for_model_classes,
        but C2 is a single model
        """

        synthesized_formulas: List[Formula] = []
        new_synthesized_formulas: List[Formula] = []
        
        # possible valuations for each sort encountered as counterexamples
        valuation_counterexamples: Dict[Sort, Set[smt.SMTTerm]] = {}
        valuation_updated = False

        with smt.Solver(name=self.solver_name) as gen_solver, \
             smt.Solver(name=self.solver_name) as check_solver: # to check that the synthesized formulas are valid

            gen_solver.add_assertion(trivial_model.get_constraint())

            for template in templates:
                template = template.strip_universal_quantifiers()

                if self.debug:
                    print(f"### synthesizing formulas of the form {template}")

                with self.solver_push(gen_solver):
                    gen_solver.add_assertion(template.get_constraint())

                    # reload all examples synthesized formulas
                    new_synthesized_formulas = synthesized_formulas

                    # not valid in some trivial model
                    extended_language = self.interpret_term_instantiations(
                        gen_solver,
                        np_indep_language,
                        Negation(template.quantify_all_free_variables()),
                        trivial_model,
                        np_indep_depth,
                    )

                    while True:
                        if valuation_updated:
                            valuation_updated = False

                            combinations = []
                            free_vars = tuple(template.get_free_variables())

                            for free_var in free_vars:
                                combinations.append(tuple(valuation_counterexamples.get(free_var.sort, ())))

                            # add all combinations of valuations
                            for assignment in itertools.product(*combinations):
                                valuation = dict(zip(free_vars, assignment))
                                gen_solver.add_assertion(template.interpret(goal_model, valuation))
                        
                        # TODO: this is buggy! may not be sufficient to rule out duplicate ones
                        # with existential variables

                        # avoid duplicates for all existing formulas
                        for formula in new_synthesized_formulas:
                            # use natural proof to check dependence
                            extended_language = self.interpret_term_instantiations(
                                gen_solver,
                                extended_language,
                                formula,
                                trivial_model,
                                np_indep_depth,
                            )
                        new_synthesized_formulas = []

                        if self.check_no_quantifiers:
                            for assertion in gen_solver.assertions:
                                assert smt.is_qfree(assertion), f"found quantified formula: {assertion.to_smtlib()}"

                        if not gen_solver.solve():
                            break

                        candidate = template.get_from_smt_model(gen_solver.get_model())
                        gen_solver.add_assertion(smt.Not(template.equals(candidate)))
                        if self.debug: print(candidate, "... ", end="", flush=True)

                        # check if the candidate is valid in all goal models
                        with self.solver_push(check_solver):
                            # when negated, the (universally quantified) free variables
                            # become existentially quantified, we do skolemization here
                            check_skolem_constants = { # for the counterexample
                                v: goal_model.interpret_sort(v.sort).get_fresh_constant(check_solver)
                                for v in template.get_free_variables()
                            }
                            check_solver.add_assertion(smt.Not(candidate.interpret(goal_model, check_skolem_constants)))

                            if check_solver.solve():
                                # found counterexample
                                if self.debug: print("✘")

                                smt_model = check_solver.get_model()

                                # update all possible valuations
                                for free_var, smt_var in check_skolem_constants.items():
                                    if free_var.sort not in valuation_counterexamples:
                                        valuation_counterexamples[free_var.sort] = set()
                                    valuation_counterexamples[free_var.sort].add(smt_model[smt_var])

                                valuation_updated = True

                                yield candidate, False

                            else:
                                # no conuterexample found
                                if self.debug: print("✓")
                                yield candidate, True
                                synthesized_formulas.append(candidate)
                                new_synthesized_formulas.append(candidate)
