from typing import Mapping, Dict, List, Set, Iterable, Generator

import synthesis.fol as fol
from synthesis.smt import smt

from .syntax import *
from .semantics import FOStructureFrame


class ModalSynthesizer:
    """
    Synthesize modal formulas in a class of frames defined by a FO sentence

    TODO: Merge this with fol.cegis.CEGISynthesizer
    """

    def __init__(self, language: fol.Language, sort_world: str, transition_symbol: str):
        self.language = language
        self.sort_world = language.get_sort(sort_world)
        self.transition_symbol = language.get_relation_symbol(transition_symbol)

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

    def check_completeness(self, goal_theory: fol.Theory, modal_axiom: Formula, blob_depth: int = 0) -> bool:
        """
        Check if the given axiom is complete for a FO characterization goal_theory
        """
        with smt.Solver(name="z3") as solver:
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

            solver.add_assertion(constraint)

            print(f"is {modal_axiom} complete (partition size {len(partition)})", end="", flush=True)

            if solver.solve():
                print(" ... ✘")

                # smt_model = solver.get_model()
                # print(complement_model.get_from_smt_model(smt_model))
                # for sc in skolemized_constants:
                #     print(smt_model[sc])

                return False
            else:
                print(" ... ✓")
                return True

    def complement_theory(self, theory: fol.Theory) -> fol.Theory:
        assert len(list(theory.get_fixpoint_definitions())) == 0
        return fol.Theory(
            theory.language,
            {},
            (
                fol.Axiom(fol.Disjunction.from_disjuncts(*(fol.Negation(axiom.formula) for axiom in theory.get_axioms()))),
            ),
        )

    def synthesize(
        self,
        formula_templates: Iterable[Formula],
        trivial_theory: fol.Theory,
        goal_theory: fol.Theory,
        model_size_bound: int = 4,
        use_negative_examples: bool = False,
        # NOTE: setting use_negative_examples to true may rule out some overapproximating formulas
    ) -> Generator[Formula, None, None]:
        # get all atoms used
        atoms: Set[Atom] = set()
        for template in formula_templates:
            atoms.update(template.get_atoms())

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

        positive_examples: List[fol.SymbolicStructure] = []
        negative_examples: List[fol.SymbolicStructure] = []
        true_formulas: List[Formula] = []

        with smt.Solver(name="z3") as solver1, \
            smt.Solver(name="z3") as solver2:

            solver1.add_assertion(trivial_model.get_constraint())
            solver2.add_assertion(goal_model.get_constraint())
            
            for formula_template in formula_templates:
                new_positive_examples = positive_examples
                new_negative_examples = negative_examples
                new_true_formulas = true_formulas

                with smt.push_solver(solver1):
                    solver1.add_assertion(formula_template.get_constraint())

                    # state that the formula should not hold on all frames
                    solver1.add_assertion(smt.Not(self.interpret_on_fo_structure(formula_template, trivial_model, atom_symbols)))

                    while True:
                        # add all positive examples
                        for positive_example in new_positive_examples:
                            # solver1.add_assertion(self.interpret_on_fo_structure(formula_template, positive_example, atom_symbols))
                            solver1.add_assertion(self.interpret_validity(formula_template, positive_example))
                        new_positive_examples = []

                        # add all negative examples
                        for negative_example in new_negative_examples:
                            solver1.add_assertion(smt.Not(self.interpret_validity(formula_template, negative_example)))
                        new_negative_examples = []
                        
                        # add all true formulas
                        for formula in new_true_formulas:
                            solver1.add_assertion(self.interpret_validity(formula, trivial_model))
                        new_true_formulas = []

                        if not solver1.solve():
                            break

                        smt_model = solver1.get_model()
                        candidate = formula_template.get_from_smt_model(smt_model)
                        candidate = candidate.simplify()
                        print(candidate, end="", flush=True)
                        
                        # new negative example
                        if use_negative_examples:
                            negative_example = trivial_model.get_from_smt_model(smt_model)
                            negative_examples.append(negative_example)
                            new_negative_examples.append(negative_example)

                        with smt.push_solver(solver2):
                            # try to find a frame in which the candidate does not hold on all worlds
                            solver2.add_assertion(smt.Not(self.interpret_on_fo_structure(candidate, goal_model, atom_symbols)))

                            if solver2.solve():
                                print(" ... ✘")
                                # add the positive_example
                                positive_example = goal_model.get_from_smt_model(solver2.get_model())
                                positive_examples.append(positive_example)
                                new_positive_examples.append(positive_example)
                            else:
                                print(" ... ✓")
                                yield candidate
                                true_formulas.append(candidate)
                                new_true_formulas.append(candidate)
