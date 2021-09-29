from typing import List, Dict, Iterable, Optional, Any
from collections import OrderedDict

from synthesis.utils.ansi import ANSI

from .base import *

from .templates import (
    QuantifierFreeFormulaTemplate,
    UnionFormulaTemplate,
    StructureTemplate,
    UninterpretedStructureTemplate,
    FiniteFOModelTemplate,
    FiniteLFPModelTemplate,
    FOProvableStructureTemplate,
)

from .utils import FOLUtils
from .prover import NaturalProof


class FOSSIL:
    SEED = 0

    @staticmethod
    def get_solver() -> smt.SMTSolver:
        return smt.Solver(name="z3", random_seed=FOSSIL.SEED, generate_models=True)

    @staticmethod
    def get_lemma_template(
        theory: Theory,
        foreground_sort: Sort,
        lemma_language: Language,
        term_depth: int,
        formula_depth: int,
        additional_free_vars: int,
    ) -> Dict[RelationSymbol, Formula]:
        fixpoint_relation_symbols = []

        for definition in theory.get_fixpoint_definitions():
            if definition.relation_symbol in lemma_language.relation_symbols:
                fixpoint_relation_symbols.append(definition.relation_symbol)

        templates: Dict[RelationSymbol, Formula] = OrderedDict() # template for each fixpoint relation
        free_vars = tuple(Variable(f"x{i}", foreground_sort) for i in range(additional_free_vars))

        free_var_index = additional_free_vars

        for relation_symbol in fixpoint_relation_symbols:
            arguments = []
            has_background_sort = False

            for sort in relation_symbol.input_sorts:
                if sort != foreground_sort:
                    has_background_sort = True
                    break

                arguments.append(Variable(f"x{free_var_index}", sort))
                free_var_index += 1

            if has_background_sort:
                continue

            assert relation_symbol not in templates, \
                f"duplicate fixpoint definitions for relation {relation_symbol}"

            rhs: Formula = QuantifierFreeFormulaTemplate(lemma_language, tuple(arguments) + free_vars, term_depth, formula_depth)

            for var in free_vars[::-1]:
                rhs = UniversalQuantification(var, rhs)

            # template for the current relation:
            # R(x) -> phi(x) 
            templates[relation_symbol] = Implication(RelationApplication(relation_symbol, tuple(arguments)), rhs).quantify_all_free_variables()

        return templates

    @staticmethod
    def get_induction_obligation(definition: FixpointDefinition, formula: Formula) -> Formula:
        """
        Given a (closed) formlua of the form
        forall x. R(x) -> phi(x)

        and the fixpoint definition of R(x) <-> rho_R(x)

        return a formula
        forall x. rho_R(x; R <- phi) -> phi(x)
        (i.e. the hypothesis in Park induction)

        This works for both concrete formulas and templates
        """

        body = formula.strip_universal_quantifiers()
        assert isinstance(body, Implication)
        assert isinstance(body.left, RelationApplication)
        assert body.left.relation_symbol == definition.relation_symbol

        free_vars = []
        for argument in body.left.arguments:
            assert isinstance(argument, Variable)
            free_vars.append(argument)

        ind_hyp = body.right

        # rho_R(x; R <- phi)
        rho_of_phi = FOLUtils.substitute_relation_application(
            definition.relation_symbol,
            ind_hyp, tuple(free_vars),
            # replace the variables in the original definition with the new variables first
            definition.definition.substitute(dict(zip(definition.variables, free_vars))),
        )

        return Implication(rho_of_phi, ind_hyp).quantify_all_free_variables()

    @staticmethod
    def get_pfp(theory: Theory, formula: Formula) -> Formula:
        body = formula.strip_universal_quantifiers()
        assert isinstance(body, Implication)
        assert isinstance(body.left, RelationApplication)

        definition = theory.find_fixpoint_definition(body.left.relation_symbol)
        assert definition is not None

        return FOSSIL.get_induction_obligation(definition, formula)

    @staticmethod
    def check_validity(theory: Theory, foreground_sort: Sort, goal: Formula, depth: int) -> bool:
        """
        Return if the goal is FO-provable under the given theory
        """
        with FOSSIL.get_solver() as solver:
            extended_language, conjuncts = NaturalProof.encode_validity(theory, foreground_sort, goal, depth)
            model = UninterpretedStructureTemplate(extended_language)

            solver.add_assertion(model.get_constraint())

            for conjunct in conjuncts:
                free_vars = conjunct.get_free_variables()
                assignment = {
                    var: model.interpret_sort(var.sort).get_fresh_constant(solver)
                    for var in free_vars
                }

                solver.add_assertion(conjunct.interpret(model, assignment))
                if not solver.solve():
                    return True

            return False

            # return not solver.solve(), extended_language, conjuncts # unsat -> valid or sat -> unprovable
            # counterexample = model.get_from_smt_model(solver.get_model()) if result else None
            # # print(counterexample)
            # return not result, counterexample

    @staticmethod
    def generate_finite_example(theory: Theory, foreground_sort: Sort, formulas: Iterable[Formula], lfp: bool = False, max_model_size: Optional[int] = None) -> Optional[Structure]:
        """
        Generate a finite model of theory such that the given formulas hold together with the theory
        """
        model_size = max_model_size or 5

        while True:
            with FOSSIL.get_solver() as solver:
                if lfp:
                    finite_model: StructureTemplate = FiniteLFPModelTemplate(theory, { foreground_sort: model_size })
                else:
                    finite_model = FiniteFOModelTemplate(theory, { foreground_sort: model_size })

                solver.add_assertion(finite_model.get_constraint())

                for formula in formulas:
                    solver.add_assertion(formula.interpret(finite_model, {}))

                if solver.solve():
                    return finite_model.get_from_smt_model(solver.get_model())

            if max_model_size is not None:
                return None

            # try again with larger size
            model_size += 1

    @staticmethod
    def prove_lfp(
        theory: Theory,
        foreground_sort: Sort,
        lemma_language: Language,
        goal: Formula,
        *_: Any,
        natural_proof_depth: int,
        lemma_term_depth: int,
        lemma_formula_depth: int,
        true_counterexample_size_bound: int,
        additional_free_vars: int = 0, # additional number of free variables (universally quantified) that can appear on the RHS of each lemma
        use_non_fo_provable_lemmas: bool = False,
        use_type1_models: bool = True,
        initial_lemmas: Iterable[Formula] = [],
    ) -> Tuple[bool, Tuple[Formula, ...]]:
        """
        The FOSSIL algorithm with all three types of counterexamples

        Return (True, lemmas) if provable
        otherwise return (False, lemmas)
        """

        lemmas: List[Formula] = list(initial_lemmas)
        lemma_templates = FOSSIL.get_lemma_template(theory, foreground_sort, lemma_language, lemma_term_depth, lemma_formula_depth, additional_free_vars)
        lemma_union_template = UnionFormulaTemplate(*lemma_templates.values()) # union of all lemma templates for each relation

        type2_models: List[Structure] = []
        # type3_models: List[Tuple[Structure, RelationSymbol]] = []

        with FOSSIL.get_solver() as synth_solver:
            synth_solver.add_assertion(lemma_union_template.get_constraint())

            if use_non_fo_provable_lemmas:
                # enforcing that the lemma should not be approximately FO provable
                fo_provable_counterexample = FOProvableStructureTemplate(theory, unfold_depth=2) # TODO: depth
                synth_solver.add_assertion(fo_provable_counterexample.get_constraint())
                synth_solver.add_assertion(smt.Not(lemma_union_template.interpret(fo_provable_counterexample, {})))
            else:
                fo_provable_counterexample = FOProvableStructureTemplate(theory, unfold_depth=0) # TODO: depth

            while True:
                validity = FOSSIL.check_validity(
                    theory.extend_axioms(lemmas),
                    foreground_sort,
                    goal,
                    natural_proof_depth,
                )

                if validity:
                    print(ANSI.in_green(f"### proved: {goal}"))
                    return True, tuple(lemmas)

                with smt.push_solver(synth_solver):
                    if use_type1_models:
                        type1_model = FOSSIL.generate_finite_example(theory.extend_axioms(lemmas), foreground_sort, [Negation(goal)])
                        assert type1_model is not None
                        synth_solver.add_assertion(smt.Not(lemma_union_template.interpret(type1_model, {})))

                    # only type 2 models are accumulated across synthesis of different lemmas
                    for type2_model in type2_models:
                        synth_solver.add_assertion(lemma_union_template.interpret(type2_model, {}))

                    # the new lemma should not be implied by the old ones
                    if not use_type1_models:
                        # if we don't use type 1 models, we need the following constraints
                        # to avoid duplicate lemmas
                        if use_non_fo_provable_lemmas:
                            # in this case such constraint can be simplified
                            for lemma in lemmas:
                                synth_solver.add_assertion(lemma.interpret(fo_provable_counterexample, {}))
                        else:
                            synth_solver.add_assertion(smt.Not(
                                smt.Implies(
                                    smt.And(
                                        lemma.interpret(fo_provable_counterexample, {})
                                        for lemma in lemmas
                                    ),
                                    lemma_union_template.interpret(fo_provable_counterexample, {}),
                                ),
                            ))

                    # try to synthesize a valid lemma
                    while True:
                        if synth_solver.solve():
                            # obtaint a concrete lemma
                            lemma = lemma_union_template.get_from_smt_model(synth_solver.get_model())
                        else:
                            print(ANSI.in_gray(f"### lemmas exhausted, unable to prove: {goal}"))
                            return False, tuple(lemmas)
                        
                        print(ANSI.in_gray(f"### lemma: {lemma}"), end="", flush=True)

                        # check if the PFP of the lemma is FO-valid under the theory and other lemmas
                        # TODO: check the types
                        lemma_pfp = FOSSIL.get_pfp(theory, lemma)

                        # sequential lemmas
                        validity = FOSSIL.check_validity(theory.extend_axioms(lemmas), foreground_sort, lemma_pfp, natural_proof_depth)

                        if validity:
                            print(ANSI.in_gray(" - ✓"))
                            lemmas.append(lemma)
                            break

                        print(ANSI.in_gray(" - ✘"), end="", flush=True)
                        synth_solver.add_assertion(smt.Not(lemma_union_template.equals(lemma)))

                        # unprovable lemma, either get a finite LFP model or finite FO model to refute it
                        model = FOSSIL.generate_finite_example(theory, foreground_sort, (Negation(lemma),), lfp=True, max_model_size=true_counterexample_size_bound)
                        if model is not None:
                            print(ANSI.in_gray(" (lfp counterexample)"))
                            print(model)
                            synth_solver.add_assertion(lemma_union_template.interpret(model, {}))
                            type2_models.append(model)

                        else:
                            # print("*** type 2 model not found, finding type 3 model")
                            # no bounded LFP model found, try to find a bounded FO model
                            type3_model = FOSSIL.generate_finite_example(theory.extend_axioms(lemmas), foreground_sort, [Negation(lemma_pfp)])
                            assert type3_model is not None

                            print(ANSI.in_gray(" (fo counterexample)"))

                            lemma_striped = lemma.strip_universal_quantifiers()
                            assert isinstance(lemma_striped, Implication) and \
                                   isinstance(lemma_striped.left, RelationApplication)

                            relation_symbol = lemma_striped.left.relation_symbol
                            pfp = FOSSIL.get_pfp(theory, lemma_templates[relation_symbol])
                            synth_solver.add_assertion(pfp.interpret(type3_model, {}))
