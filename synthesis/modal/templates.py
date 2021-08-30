from typing import Tuple, Callable

from synthesis.template import Template, BoundedIntegerVariable

from .syntax import *


class ModalFormulaTemplate(Formula):
    def __init__(self, atoms: Tuple[Atom, ...], depth: int):
        self.atoms = atoms
        self.node = BoundedIntegerVariable(0, 9 + len(atoms))
        self.depth = depth

        if depth == 0:
            self.subformulas: Tuple[ModalFormulaTemplate, ...] = ()
        else:
            self.subformulas = (
                ModalFormulaTemplate(atoms, depth - 1),
                ModalFormulaTemplate(atoms, depth - 1),
            )

    def get_constructor_and_arity(self, node_value: int) -> Tuple[Callable[..., Formula], int]:
        return {
            # 0 for null
            1: (Falsum, 0),
            2: (Verum, 0),
            3: (Conjunction, 2),
            4: (Disjunction, 2),
            5: (Implication, 2),
            6: (Equivalence, 2),
            7: (Negation, 1),
            8: (Modality, 1),
            9: (Diamond, 1),
            # the rest is for atoms
        }[node_value]

    def get_is_null_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.node.equals(0),
            *(subformula.get_is_null_constraint() for subformula in self.subformulas),
        )

    def get_constraint(self) -> smt.SMTTerm:
        constraint = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value > 9:
                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        *(subformula.get_is_null_constraint() for subformula in self.subformulas),
                    ),
                    constraint,
                )
            
            elif node_value != 0 and self.depth != 0:
                _, arity = self.get_constructor_and_arity(node_value)
                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        *(subformula.get_constraint() for subformula in self.subformulas[:arity]),
                        *(subformula.get_is_null_constraint() for subformula in self.subformulas[arity:]),
                    ),
                    constraint,
                )

        return constraint

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        node_value = self.node.get_from_smt_model(model)
        assert node_value != 0, "null formula"

        if node_value <= 9:
            constructor, arity = self.get_constructor_and_arity(node_value)
            return constructor(*(subformula.get_from_smt_model(model) for subformula in self.subformulas[:arity]))

        return self.atoms[node_value - 10]

    def equals(self, value: Formula) -> smt.SMTTerm:
        if isinstance(value, Falsum):
            return self.node.equals(1)

        if isinstance(value, Verum):
            return self.node.equals(2)

        if isinstance(value, Atom):
            if value in self.atoms:
                return self.node.equals(10 + self.atoms.index(value))
            else:
                return smt.FALSE()

        if self.depth == 0:
            return smt.FALSE()

        if isinstance(value, Conjunction):
            return smt.And(
                self.node.equals(3),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )
        
        if isinstance(value, Disjunction):
            return smt.And(
                self.node.equals(4),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )

        if isinstance(value, Implication):
            return smt.And(
                self.node.equals(5),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )

        if isinstance(value, Equivalence):
            return smt.And(
                self.node.equals(6),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )

        if isinstance(value, Negation):
            return smt.And(
                self.node.equals(7),
                self.subformulas[0].equals(value.formula),
            )

        if isinstance(value, Modality):
            return smt.And(
                self.node.equals(8),
                self.subformulas[0].equals(value.formula),
            )

        if isinstance(value, Diamond):
            return smt.And(
                self.node.equals(9),
                self.subformulas[0].equals(value.formula),
            )
        
        return smt.FALSE()

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        interp = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value > 9:
                interp = smt.Ite(
                    self.node.equals(node_value),
                    self.atoms[node_value - 10].interpret(frame, valuation, world),
                    interp,
                )

            elif node_value == 1:
                interp = smt.Ite(
                    self.node.equals(node_value),
                    smt.FALSE(),
                    interp,
                )

            elif node_value == 2:
                interp = smt.Ite(
                    self.node.equals(node_value),
                    smt.TRUE(),
                    interp,
                )

            elif self.depth != 0:
                if node_value == 3:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.And(
                            self.subformulas[0].interpret(frame, valuation, world),
                            self.subformulas[1].interpret(frame, valuation, world),
                        ),
                        interp,
                    )

                elif node_value == 4:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Or(
                            self.subformulas[0].interpret(frame, valuation, world),
                            self.subformulas[1].interpret(frame, valuation, world),
                        ),
                        interp,
                    )

                elif node_value == 5:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Implies(
                            self.subformulas[0].interpret(frame, valuation, world),
                            self.subformulas[1].interpret(frame, valuation, world),
                        ),
                        interp,
                    )

                elif node_value == 6:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Iff(
                            self.subformulas[0].interpret(frame, valuation, world),
                            self.subformulas[1].interpret(frame, valuation, world),
                        ),
                        interp,
                    )

                elif node_value == 7:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Not(self.subformulas[0].interpret(frame, valuation, world)),
                        interp,
                    )

                elif node_value == 8:
                    var = frame.get_fresh_constant()
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        frame.universally_quantify(
                            var,
                            smt.Implies(
                                frame.interpret_transition(world, var),
                                self.subformulas[0].interpret(frame, valuation, var),
                            ),
                        ),
                        interp,
                    )

                elif node_value == 9:
                    var = frame.get_fresh_constant()
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        frame.existentially_quantify(
                            var,
                            smt.And(
                                frame.interpret_transition(world, var),
                                self.subformulas[0].interpret(frame, valuation, var),
                            ),
                        ),
                        interp,
                    )

        return interp
