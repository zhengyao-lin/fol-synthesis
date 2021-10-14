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

    def interpret_validity(self, formula: Formula, finite_structure: fol.FiniteFOModelTemplate) -> smt.SMTTerm:
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
            # complement_model = fol.FiniteFOModelTemplate(fol.Theory.empty_theory(self.language), { self.sort_world: 7 })
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

                # other_truth_value_constraint = smt.And(
                #     other_truth_value_constraint,
                #     smt.And(
                #         smt.Implies(smt.Equals(skolemized_world1, skolemized_world2), smt.Iff(successor_truth_value1, successor_truth_value2))
                #         for skolemized_world1, successor_truth_value1 in zip(skolemized_constants, other_truth_values)
                #         for skolemized_world2, successor_truth_value2 in zip(skolemized_constants, other_truth_values)
                #     ),
                # )

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
                model = solver.get_model()
                # print(*(model.get_value(c) for c in skolemized_constants))
                # print(complement_model.get_from_smt_model(model))
                return False
            else:
                print(" ... ✓")
                return True

    def synthesize(
        self,
        formula_templates: Iterable[Formula],
        trivial_theory: fol.Theory,
        goal_theory: fol.Theory,
        model_size_bound: int = 4,
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
        trivial_theory = trivial_theory.expand_language(language_expansion)
        goal_theory = goal_theory.expand_language(language_expansion)

        trivial_model = fol.FiniteFOModelTemplate(trivial_theory, { self.sort_world: model_size_bound })
        goal_model = fol.FiniteFOModelTemplate(goal_theory, { self.sort_world: model_size_bound })

        counterexamples: List[fol.Structure] = []
        true_formulas: List[Formula] = []

        with smt.Solver(name="z3") as solver1, \
            smt.Solver(name="z3") as solver2:

            solver1.add_assertion(trivial_model.get_constraint())
            solver2.add_assertion(goal_model.get_constraint())
            
            for formula_template in formula_templates:
                new_counterexamples = counterexamples
                new_true_formulas = true_formulas

                with smt.push_solver(solver1):
                    solver1.add_assertion(formula_template.get_constraint())

                    # state that the formula should not hold on all frames
                    solver1.add_assertion(smt.Not(self.interpret_on_fo_structure(formula_template, trivial_model, atom_symbols)))

                    while True:
                        # add all counterexamples and true formulas
                        for counterexample in new_counterexamples:
                            solver1.add_assertion(self.interpret_on_fo_structure(formula_template, counterexample, atom_symbols))
                        new_counterexamples = []
                        
                        for formula in new_true_formulas:
                            solver1.add_assertion(self.interpret_validity(formula, trivial_model))
                        new_true_formulas = []

                        if not solver1.solve():
                            break

                        candidate = formula_template.get_from_smt_model(solver1.get_model())
                        print(candidate, end="", flush=True)

                        with smt.push_solver(solver2):
                            # try to find a frame in which the ca`ndidate does not hold on all worlds
                            solver2.add_assertion(smt.Not(self.interpret_on_fo_structure(candidate, goal_model, atom_symbols)))

                            if solver2.solve():
                                print(" ... ✘")
                                # add the counterexample
                                counterexample = goal_model.get_from_smt_model(solver2.get_model())
                                counterexamples.append(counterexample)
                                new_counterexamples.append(counterexample)
                            else:
                                print(" ... ✓")
                                yield candidate
                                true_formulas.append(candidate)
                                new_true_formulas.append(candidate)
