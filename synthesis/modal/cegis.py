from typing import Mapping, Dict, List, Set, Iterable, Generator, Optional, TextIO

import sys
from enum import Enum
from contextlib import nullcontext

import synthesis.fol as fol
from synthesis.smt import smt
from synthesis.utils.stopwatch import Stopwatch

from .syntax import *
from .semantics import FOStructureFrame


class FormulaResultType(Enum):
    GOOD = 1 # good enough (i.e. passed all of the checks)
    DEPENDENT = 2 # (could be) dependent
    COUNTEREXAMPLE = 3 # (definitely) unsound and found counterexample
    UNSOUND = 4 # (definitely) unsound but did not find a counterexample
    PRUNED = 5 # later pruned in a separate dependency check


class ModalSynthesizer:
    """
    Synthesize modal formulas in a class of frames defined by a FO sentence

    TODO: Merge this with fol.cegis.CEGISynthesizer
    """

    def __init__(
        self,
        language: fol.Language,
        sort_world: str,
        transition_symbol: str,
        solver_seed: int = 0,
        output: TextIO = sys.stderr,
    ):
        self.language = language
        self.sort_world = language.get_sort(sort_world)
        self.transition_symbol = language.get_relation_symbol(transition_symbol)
        self.solver_seed = solver_seed
        self.output = output

    @staticmethod
    def get_atom_interpretation_in_structure(
        structure: fol.Structure,
        atom_symbols: Mapping[Atom, fol.RelationSymbol]
    ) -> Dict[Atom, smt.SMTFunction]:
        return {
            atom: (lambda symbol: lambda world: structure.interpret_relation(symbol, world))(symbol)
            for atom, symbol in atom_symbols.items()
        }
    
    def interpret_on_fo_structure(
        self,
        formula: Formula,
        structure: fol.Structure,
        atom_symbols: Mapping[Atom, fol.RelationSymbol],
    ) -> smt.SMTTerm:
        return formula.interpret_on_all_worlds(
            FOStructureFrame(structure, self.sort_world, self.transition_symbol),
            self.get_atom_interpretation_in_structure(structure, atom_symbols),
        )

    def interpret_validity(self, formula: Formula, finite_structure: fol.SymbolicStructure) -> smt.SMTTerm:
        """
        Same as interpret_on_fo_structure but quantifies over all valuations
        """
        all_variables: List[smt.SMTTerm] = []
        valuation: Dict[Atom, smt.SMTFunction] = {}

        for atom in formula.get_atoms():
            relation, variables = finite_structure.get_free_finite_relation((self.sort_world,))
            valuation[atom] = relation
            all_variables.extend(variables)

        return smt.ForAll(all_variables, formula.interpret_on_all_worlds(
            FOStructureFrame(finite_structure, self.sort_world, self.transition_symbol),
            valuation,
        ))

    def construct_blobs(self, model: fol.Structure, base_worlds: Iterable[smt.SMTTerm], depth: int) -> Tuple[smt.SMTFunction, ...]:
        """
        Returns (base worlds, a partition (list of predicates))

        Let n = base_size, d = depth
        The total number of blobs will be bounded by 2^(n(d + 1))
        """

        carrier_world = model.interpret_sort(self.sort_world)
        world_smt_sort = carrier_world.get_smt_sort()

        # predicates saying that a world is a k-successor of some base world, for some k
        successor_classes: List[smt.SMTFunction] = []

        for base_world in base_worlds:
            for k in range(depth + 1):
                if k == 0:
                    successor_classes.append((lambda base_world: lambda world: smt.Equals(world, base_world))(base_world))
                else:
                    path = (base_world,) + tuple(smt.FreshSymbol(world_smt_sort) for _ in range(k))
                    connected_constraint = smt.And(
                        model.interpret_relation(self.transition_symbol, path[i], path[i + 1])
                        for i in range(k)
                    )

                    # existentially quantify all intermediate worlds
                    for i in range(1, k):
                        connected_constraint = carrier_world.existentially_quantify(path[i], connected_constraint)

                    successor_classes.append((lambda connected_constraint, last_world: lambda world:
                        connected_constraint.substitute({ last_world: world })
                    )(connected_constraint, path[-1]))

        # add all paritions (some might be empty for some instantiation of base_worlds)
        partition: List[smt.SMTFunction] = []

        for switches in range(2 ** len(successor_classes)):
            partition.append((lambda switches: lambda world:
                smt.And(
                    successor_class(world) if switches & (1 << i) != 0 else smt.Not(successor_class(world))
                    for i, successor_class in enumerate(successor_classes)
                )
            )(switches))

        return tuple(partition)

    def get_valuation_on_partition(self, partition: Tuple[smt.SMTFunction, ...]) -> Tuple[Tuple[smt.SMTVariable, ...], smt.SMTFunction]:
        """
        Return a unary relation on worlds that's variable only across equivalence classes

        Assume that the partition is indeed a partition
        """

        valuation_vars = tuple(smt.FreshSymbol(smt.BOOL) for _ in partition)

        return valuation_vars, lambda world: smt.Or(
            smt.And(eq_class(world), truth)
            for eq_class, truth in zip(partition, valuation_vars)
        )

    def check_completeness(
        self,
        goal_theory: fol.Theory,
        modal_axiom: Formula,
        blob_depth: int = 0,
        timeout: int = 0,
    ) -> bool:
        """
        Check if the given axiom is complete for a FO characterization goal_theory
        timeout <= 0 for no timeout
        """
        options = {}
        if timeout >= 0:
            options["timeout"] = timeout

        with smt.Solver(name="z3", random_seed=self.solver_seed, solver_options=options) as solver:
            # check that the axiom does not hold on a non-model of the goal_theory
            complement_model = fol.FOModelTemplate(fol.Theory.empty_theory(self.language), default_sort=smt.INT)
            # complement_model = fol.FiniteFOModelTemplate(fol.Theory.empty_theory(self.language), { self.sort_world: 6 })
            solver.add_assertion(complement_model.get_constraint())

            carrier_world = complement_model.interpret_sort(self.sort_world)
            skolemized_constants: List[smt.SMTTerm] = []
            complement_constraint = smt.FALSE()

            # negate each axiom and skolemize
            for axiom in goal_theory.get_axioms():
                formula = axiom.formula
                assignment: Dict[fol.Variable, smt.SMTTerm] = {}

                while isinstance(formula, fol.UniversalQuantification) and \
                      formula.variable.sort == self.sort_world:
                    constant = carrier_world.get_fresh_constant(solver)
                    skolemized_constants.append(constant)
                    assignment[formula.variable] = constant
                    formula = formula.body

                complement_constraint = smt.Or(
                    complement_constraint,
                    smt.Not(formula.interpret(complement_model, assignment)),
                )

            solver.add_assertion(complement_constraint)

            partition = self.construct_blobs(complement_model, skolemized_constants, blob_depth)

            # for each atom, create a valuation constant in each equivalence class of <partition>
            all_valuation_vars: List[smt.SMTVariable] = []
            valuations: Dict[Atom, smt.SMTFunction] = {}

            for atom in modal_axiom.get_atoms():
                valuation_vars, valuation = self.get_valuation_on_partition(partition)
                all_valuation_vars.extend(valuation_vars)
                valuations[atom] = valuation

            # temporary placeholder for the world
            world_var = smt.FreshSymbol(complement_model.get_smt_sort(self.sort_world))

            # quantify over all valuations (with finite basis)
            constraint = smt.ForAll(all_valuation_vars,
                modal_axiom.interpret(
                    FOStructureFrame(complement_model, self.sort_world, self.transition_symbol),
                    valuations,
                    world_var,
                ),
            )

            # quantify over all skolemized constants/worlds
            constraint = smt.And(
                constraint.substitute({ world_var: constant })
                for constant in skolemized_constants
            )

            # for constant in skolemized_constants:
            #     constraint = carrier_world.universally_quantify(constant, constraint)

            solver.add_assertion(constraint)

            return not solver.solve()

            # print(f"is {modal_axiom} complete ({len(skolemized_constants)} base world(s), partition size {len(partition)})",
            #       end="", flush=True, file=self.output)

            # if solver.solve():
            #     print(" ... ✘", file=self.output)

            #     # smt_model = solver.get_model()
            #     # print(complement_model.get_from_smt_model(smt_model))
            #     # for sc in skolemized_constants:
            #     #     print(smt_model[sc])

            #     return False
            # else:
            #     print(" ... ✓", file=self.output)
            #     return True

    def complement_theory(self, theory: fol.Theory) -> fol.Theory:
        assert len(list(theory.get_fixpoint_definitions())) == 0
        return fol.Theory(
            theory.language,
            {},
            (
                fol.Axiom(fol.Disjunction.from_disjuncts(*(fol.Negation(axiom.formula) for axiom in theory.get_axioms()))),
            ),
        )

    def check_validity(
        self,
        goal_theory: fol.Theory,
        axiom: Formula,
    ) -> bool:
        """
        Check if the given modal formula is valid in the goal theory
        """
        atoms = axiom.get_atoms()
        atom_interpretatins = {}

        for atom in atoms:
            atom_interpretatins[atom] = fol.RelationSymbol((self.sort_world,), atom.name)

        with smt.Solver(name="z3", random_seed=self.solver_seed) as solver:
            extended_theory = goal_theory.expand_language(fol.Language(
                (self.sort_world,),
                (),
                tuple(atom_interpretatins.values()),
            ))

            goal_model = fol.FOModelTemplate(extended_theory)

            solver.add_assertion(goal_model.get_constraint())
            solver.add_assertion(smt.Not(self.interpret_on_fo_structure(axiom, goal_model, atom_interpretatins)))

            try:
                return not solver.solve()
            except:
                return False

    def get_trivial_theory(self) -> fol.Theory:
        language = fol.Language(
            sorts=(self.sort_world,),
            function_symbols=(),
            relation_symbols=(self.transition_symbol,),
        )

        return fol.Theory(language, {}, ())

    def check_modal_entailment(
        self,
        axioms: Iterable[Formula],
        goal: Formula,
        model_size_bound: int = 4,
    ) -> bool:
        """
        Checks if axioms |= goal in modal logic

        Returns
        - False if found witness that axioms not |= goal
        - True if no witness found (but it's not necessarily true that axioms |= goal)
        """

        atoms: Set[Atom] = goal.get_atoms()
        for axiom in axioms:
            atoms.update(axiom.get_atoms())

        atom_symbols: Dict[Atom, fol.RelationSymbol] = {}

        # create a relation symbol for each atom
        for atom in atoms:
            atom_symbols[atom] = fol.RelationSymbol((self.sort_world,), atom.name.capitalize())

        trivial_theory = self.get_trivial_theory() \
                             .expand_language(fol.Language((), (), tuple(atom_symbols.values())))

        trivial_model = fol.FiniteFOModelTemplate(trivial_theory, { self.sort_world: model_size_bound })

        with smt.Solver(name="z3", random_seed=self.solver_seed) as solver:
            solver.add_assertion(trivial_model.get_constraint())

            for axiom in axioms:
                solver.add_assertion(self.interpret_validity(axiom, trivial_model))

            solver.add_assertion(smt.Not(self.interpret_on_fo_structure(goal, trivial_model, atom_symbols)))

            return not solver.solve()

    def synthesize(
        self,
        formula_templates: Iterable[Formula],
        trivial_theory: fol.Theory,
        goal_theory: fol.Theory,
        model_size_bound: int = 4,
        use_positive_examples: bool = True,
        use_negative_examples: bool = False, # NOTE: setting use_negative_examples to true may rule out some overapproximating formulas
        check_soundness: bool = False,
        separate_independence: bool = False, # NOTE: this set to true will disable use_negative_examples
        use_enumeration: bool = False, # replace solver_synthesis with enumeration
        stopwatch: Optional[Stopwatch] = None,
    ) -> Generator[Tuple[Formula, FormulaResultType], None, None]:
        # get all atoms used
        atoms: Set[Atom] = set()
        for template in formula_templates:
            atoms.update(template.get_atoms())

        # TODO: this may introduce non-determinism
        atom_symbols: Dict[Atom, fol.RelationSymbol] = {}

        # create a relation symbol for each atom
        for atom in atoms:
            atom_symbols[atom] = fol.RelationSymbol((self.sort_world,), atom.name.capitalize())

        # expand the language with new predicates
        language_expansion = fol.Language((), (), tuple(atom_symbols.values()))
        goal_theory = goal_theory.expand_language(language_expansion)

        if use_negative_examples:
            trivial_theory = self.complement_theory(goal_theory)
        else:
            trivial_theory = trivial_theory.expand_language(language_expansion)

        trivial_model = fol.FiniteFOModelTemplate(trivial_theory, { self.sort_world: model_size_bound })
        goal_model = fol.FiniteFOModelTemplate(goal_theory, { self.sort_world: model_size_bound })

        # These lists persist across synthesis of different templates
        positive_examples: List[fol.SymbolicStructure] = []
        negative_examples: List[fol.SymbolicStructure] = []
        true_formulas: List[Formula] = []
        excluded_formulas: List[Formula] = [] # formulas to **syntactically** exclude

        with smt.Solver(name="z3", random_seed=self.solver_seed) as solver_synthesis, \
             smt.Solver(name="z3", random_seed=self.solver_seed) as solver_independence, \
             smt.Solver(name="z3", random_seed=self.solver_seed) as solver_counterexample:

            with stopwatch.time("encoding"):
                if separate_independence:
                    solver_independence.add_assertion(trivial_model.get_constraint())
                else:
                    solver_synthesis.add_assertion(trivial_model.get_constraint())

                solver_counterexample.add_assertion(goal_model.get_constraint())
            
            for formula_template in formula_templates:
                new_positive_examples = positive_examples
                new_negative_examples = negative_examples
                new_true_formulas = true_formulas
                new_excluded_formulas = excluded_formulas

                # Only used if use_enumeration == True
                # TODO: add a default enumerator for all templates
                enumerator = formula_template.enumerate()
                enumerator_count = 0

                with (smt.push_solver(solver_synthesis) if not use_enumeration else nullcontext()):
                    with stopwatch.time("encoding"):
                        solver_synthesis.add_assertion(formula_template.get_constraint())

                        # state that the formula should not hold on frames where
                        # true_formulas hold (initially true_formulas = [] so all frames)
                        if not separate_independence:
                            solver_synthesis.add_assertion(smt.Not(self.interpret_on_fo_structure(formula_template, trivial_model, atom_symbols)))

                    while True:
                        if not use_positive_examples:
                            positive_examples = []

                        if not use_negative_examples:
                            negative_examples = []

                        # add all positive examples
                        if not use_enumeration:
                            with stopwatch.time("encoding"):
                                for positive_example in new_positive_examples:
                                    # solver_synthesis.add_assertion(self.interpret_on_fo_structure(formula_template, positive_example, atom_symbols))
                                    solver_synthesis.add_assertion(self.interpret_validity(formula_template, positive_example))
                        new_positive_examples = []

                        # add all negative examples
                        if not use_enumeration:
                            with stopwatch.time("encoding"):
                                for negative_example in new_negative_examples:
                                    solver_synthesis.add_assertion(smt.Not(self.interpret_validity(formula_template, negative_example)))
                        new_negative_examples = []
                        
                        # add all true formulas
                        with stopwatch.time("encoding"):
                            for formula in new_true_formulas:
                                if separate_independence:
                                    solver_independence.add_assertion(self.interpret_validity(formula, trivial_model))
                                else:
                                    if not use_enumeration:
                                        solver_synthesis.add_assertion(self.interpret_validity(formula, trivial_model))
                        new_true_formulas = []

                        # add all excluded formulas
                        if not use_enumeration:
                            with stopwatch.time("encoding"):
                                for formula in new_excluded_formulas:
                                    solver_synthesis.add_assertion(smt.Not(formula_template.equals(formula)))
                        new_excluded_formulas = []

                        if use_enumeration:
                            try:
                                with stopwatch.time("synthesis"):
                                    while True:
                                        candidate = next(enumerator)
                                        enumerator_count += 1
                                        print(f"\r[enumerated {enumerator_count}]", end="")
                                        print(candidate, end="", flush=True, file=self.output)

                                        # check whether the candidate holds on positive and negative examples
                                        failed_check = False

                                        if not failed_check and use_positive_examples:
                                            for positive_example in positive_examples:
                                                if self.interpret_validity(candidate, positive_example).simplify().is_false():
                                                    # failed a positive example
                                                    failed_check = True
                                                    print(f" ... ✘ (failed positive example)", file=self.output)
                                                    break

                                        if not failed_check and use_negative_examples:
                                            for negative_example in negative_examples:
                                                if self.interpret_validity(candidate, negative_example).simplify().is_true():
                                                    # failed a negative example
                                                    failed_check = True
                                                    print(f" ... ✘ (failed negative example)", file=self.output)
                                                    break

                                        if not failed_check:
                                            break

                            except StopIteration:
                                break
                        else:
                            with stopwatch.time("synthesis"):
                                if not solver_synthesis.solve():
                                    break
                                smt_model = solver_synthesis.get_model()
                                candidate = formula_template.get_from_smt_model(smt_model)
                                # candidate = candidate.simplify()

                            print(candidate, end="", flush=True, file=self.output)
                        
                        # new negative example
                        if not separate_independence:
                            if use_negative_examples:
                                negative_example = trivial_model.get_from_smt_model(smt_model)
                                negative_examples.append(negative_example)
                                new_negative_examples.append(negative_example)

                        if separate_independence:
                            # Perform a separate check of independence
                            # i.e. whether there is a small model where
                            # all of true_formulas hold but the candidate
                            # does not hold
                            with smt.push_solver(solver_independence):
                                with stopwatch.time("encoding"):
                                    solver_independence.add_assertion(smt.Not(self.interpret_on_fo_structure(candidate, trivial_model, atom_symbols)))

                                with stopwatch.time("independence"):
                                    solver_result = solver_independence.solve()

                                if solver_result:
                                    # found witness to independence, continue
                                    pass

                                else:
                                    # no witness found
                                    # NOTE: in this case, the axiom may still be independent
                                    print(" ... ✘ (no independence witness found)", file=self.output)
                                    excluded_formulas.append(candidate)
                                    new_excluded_formulas.append(candidate)
                                    yield candidate, FormulaResultType.DEPENDENT
                                    continue

                        with smt.push_solver(solver_counterexample):
                            # try to find a frame in which the candidate does not hold on all worlds
                            with stopwatch.time("encoding"):
                                solver_counterexample.add_assertion(smt.Not(self.interpret_on_fo_structure(candidate, goal_model, atom_symbols)))

                            with stopwatch.time("counterexample"):
                                solver_result = solver_counterexample.solve()

                            if solver_result:
                                print(" ... ✘ (counterexample)", file=self.output)

                                if use_positive_examples:
                                    # add the positive_example
                                    positive_example = goal_model.get_from_smt_model(solver_counterexample.get_model())
                                    positive_examples.append(positive_example)
                                    new_positive_examples.append(positive_example)
                                else:
                                    excluded_formulas.append(candidate)
                                    new_excluded_formulas.append(candidate)

                                yield candidate, FormulaResultType.COUNTEREXAMPLE
                            else:
                                if check_soundness:
                                    with stopwatch.time("soundness"):
                                        sound = self.check_validity(goal_theory, candidate)
                                    
                                    if not sound:
                                        print(" ... ✘ (unsound)", file=self.output)
                                        excluded_formulas.append(candidate)
                                        new_excluded_formulas.append(candidate)
                                        yield candidate, FormulaResultType.UNSOUND
                                        continue

                                print(" ... ✓", file=self.output)
                                true_formulas.append(candidate)
                                new_true_formulas.append(candidate)

                                yield candidate, FormulaResultType.GOOD
