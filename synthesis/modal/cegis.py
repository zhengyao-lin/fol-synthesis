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

    def check_completeness(self, goal_theory: fol.Theory, modal_axiom: Formula) -> bool:
        """
        Check if the given axiom is complete for a FO characterization goal_theory
        """
        atoms = modal_axiom.get_atoms()

        with smt.Solver(name="z3") as solver:
            # check that the axiom does not hold on a non-model of the goal_theory
            complement_model = fol.FOModelTemplate(fol.Theory.empty_theory(self.language))
            # complement_model = fol.FiniteFOModelTemplate(fol.Theory.empty_theory(self.language), { self.sort_world: 3 }, exact_size=True)
            solver.add_assertion(complement_model.get_constraint())

            carrier_world = complement_model.interpret_sort(self.sort_world)
            skolemized_constants: List[smt.SMTTerm] = []

            for axiom in goal_theory.get_axioms():
                formula = axiom.formula
                assignment: Dict[fol.Variable, smt.SMTTerm] = {}

                while isinstance(formula, fol.UniversalQuantification) and \
                      formula.variable.sort == self.sort_world:
                    constant = carrier_world.get_fresh_constant(solver)
                    skolemized_constants.append(constant)
                    assignment[formula.variable] = constant
                    formula = formula.body

                solver.add_assertion(smt.Not(formula.interpret(complement_model, assignment)))

            print(f"checking valuations on {len(skolemized_constants)} skolemized constant(s)")

            valuation_variables: List[smt.SMTTerm] = []
            valuations: Dict[Atom, smt.SMTFunction] = {}

            # other_truth_value_constraint = smt.TRUE()

            # for each atom, create a relation that is constant outside skolemized_constants
            for atom in atoms:
                # truth value for each skolemized_constants
                truth_values = tuple(smt.FreshSymbol(smt.BOOL) for _ in skolemized_constants)

                # truth outside skolemized_constants
                # other_truth_value = smt.FreshSymbol(smt.BOOL)

                # for successors of each skolemized constant,
                # we assign a (potentially different) truth value 
                blob_truth_values = tuple(smt.FreshSymbol(smt.BOOL) for _ in skolemized_constants)

                other_truth_value = smt.FreshSymbol(smt.BOOL)

                relation = (lambda truth_values, blob_truth_values, other_truth_value: lambda world: smt.Or(
                    smt.Or(
                        smt.And(
                            smt.Equals(world, skolemized_world),
                            truth_value,
                        )
                        for skolemized_world, truth_value in zip(skolemized_constants, truth_values)
                    ),
                    smt.Or(
                        smt.And(
                            smt.And(
                                smt.Not(smt.Equals(world, skolemized_world))
                                for skolemized_world in skolemized_constants
                            ),
                            # other_truth_value,
                            smt.Or(
                                smt.Or(
                                    smt.And(
                                        smt.And(
                                            complement_model.interpret_relation(self.transition_symbol, skolemized_world, world),
                                            smt.And(
                                                # so that we don't assign duplicate values to a world
                                                smt.And(
                                                    smt.Not(smt.Equals(skolemized_world, other_skolemized_world)),
                                                    smt.Not(complement_model.interpret_relation(self.transition_symbol, other_skolemized_world, world)),
                                                )
                                                for other_skolemized_world in skolemized_constants[i + 1:]
                                            ),
                                        ),
                                        successor_truth_value,
                                    )
                                    for i, (skolemized_world, successor_truth_value) in enumerate(zip(skolemized_constants, blob_truth_values))
                                ),
                                smt.And(
                                    smt.And(
                                        smt.Not(complement_model.interpret_relation(self.transition_symbol, skolemized_world, world))
                                        for skolemized_world in skolemized_constants
                                    ),
                                    other_truth_value,
                                ),
                            ),
                        ),
                    ),
                ))(truth_values, blob_truth_values, other_truth_value)

                valuations[atom] = relation
                valuation_variables.extend(truth_values)
                valuation_variables.extend(blob_truth_values)
                valuation_variables.append(other_truth_value)

            # temporary placeholder for the world
            world_var = smt.FreshSymbol(complement_model.get_smt_sort(self.sort_world))

            # quantify over all valuations (with finite basis)
            constraint = smt.ForAll(valuation_variables,
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

            print(f"is {modal_axiom} complete", end="", flush=True)

            if solver.solve():
                print(" ... ✘")
                # print(complement_model.get_from_smt_model(solver.get_model()))
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
