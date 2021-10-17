from typing import Tuple, Callable, Type, List

from synthesis.template import Template, BoundedIntegerVariable, UnionTemplate

from .syntax import *


class UnionFormulaTemplate(UnionTemplate[Formula], Formula):
    templates: Tuple[Formula, ...]

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Or(*(
            smt.Ite(
                self.node.equals(node_value),
                template.interpret(frame, valuation, world),
                smt.FALSE(),
            )
            for node_value, template in enumerate(self.templates, 1)
        ))

    def get_atoms(self) -> Set[Atom]:
        atoms = set()
        for template in self.templates:
            atoms.update(template.get_atoms())
        return atoms


class ModalFormulaTemplate(Formula):
    def __init__(self, atoms: Tuple[Atom, ...], connectives: Tuple[Type[Formula], ...], depth: int):
        self.atoms = atoms
        self.connectives = connectives
        self.node = BoundedIntegerVariable(0, len(atoms) + len(connectives))
        self.depth = depth

        # node values:
        # 0 for null
        # [1, len(atoms)] for atoms
        # [len(atoms) + 1, len(atoms) + len(connectives)] for connectives

        max_arity = 0 if len(connectives) == 0 else max((connective.get_arity() for connective in connectives))

        if depth == 0:
            self.subformulas: Tuple[ModalFormulaTemplate, ...] = ()
        else:
            self.subformulas = tuple(
                ModalFormulaTemplate(atoms, connectives, depth - 1)
                for _ in range(max_arity)
            )

    @classmethod
    def get_arity(cls) -> int:
        raise NotImplementedError()

    def get_immediate_subformulas(self) -> Tuple[Formula, ...]:
        raise NotImplementedError()

    def inductive_interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], subformulas: Tuple[Interpretation, ...]) -> Interpretation:
        raise NotImplementedError()

    def get_atoms(self) -> Set[Atom]:
        return set(self.atoms)

    def get_is_null_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.node.equals(0),
            *(subformula.get_is_null_constraint() for subformula in self.subformulas),
        )

    def get_constraint(self) -> smt.SMTTerm:
        constraint = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value == 0:
                continue

            if node_value <= len(self.atoms):
                # atoms
                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        *(subformula.get_is_null_constraint() for subformula in self.subformulas),
                    ),
                    constraint,
                )

            else:
                # connective
                connective_idx = node_value - len(self.atoms) - 1
                arity = self.connectives[connective_idx].get_arity()

                if arity != 0 and self.depth == 0:
                    continue

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

        if node_value <= len(self.atoms):
            return self.atoms[node_value - 1]

        assert node_value <= len(self.atoms) + len(self.connectives), \
               "invalid node value"

        connective_idx = node_value - len(self.atoms) - 1
        connective = self.connectives[connective_idx]
        arity = connective.get_arity()
        return connective(*(subformula.get_from_smt_model(model) for subformula in self.subformulas[:arity]))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if isinstance(value, Atom):
            if value in self.atoms:
                return self.node.equals(self.atoms.index(value) + 1)
            else:
                return smt.FALSE()
        elif self.depth == 0:
            return smt.FALSE()

        constraint = smt.FALSE()

        for idx, connective in enumerate(self.connectives):
            if isinstance(value, connective):
                subformulas = value.get_immediate_subformulas()
                assert len(subformulas) == connective.get_arity()
                constraint = smt.Or(
                    constraint,
                    smt.And(
                        self.node.equals(idx + len(self.atoms) + 1),
                        smt.And((
                            template.equals(concrete)
                            for template, concrete in zip(self.subformulas[:connective.get_arity()], subformulas)
                        )),
                    ),
                )

        return constraint

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        interp = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value == 0:
                continue

            if node_value <= len(self.atoms):
                interp = smt.Ite(
                    self.node.equals(node_value),
                    self.atoms[node_value - 1].interpret(frame, valuation, world),
                    interp,
                )
            else:
                connective_idx = node_value - len(self.atoms) - 1
                connective = self.connectives[connective_idx]
                arity = connective.get_arity()

                # only have null-ary connectives if the depth is 0
                if arity != 0 and self.depth == 0:
                    continue

                # delegate interpretation to the actual implementation of the connective
                interp = smt.Ite(
                    self.node.equals(node_value),
                    connective(*self.subformulas[:arity]).interpret(frame, valuation, world),
                    interp,
                )
                
        return interp
