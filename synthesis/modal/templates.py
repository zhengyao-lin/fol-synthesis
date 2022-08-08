from typing import Tuple, Callable, List, Any, Generator, Dict

import itertools

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


@dataclass
class Connective:
    constructor: Callable[..., Formula]
    arity: int

    def get_arity(self) -> int:
        return self.arity

    def construct(self, *args: Any) -> Formula:
        assert len(args) == self.arity
        return self.constructor(*args)


class ModalFormulaTemplate(Formula):
    def __init__(self, atoms: Tuple[Atom, ...], connectives: Tuple[Connective, ...], depth: int):
        self.atoms = atoms
        self.connectives = connectives
        self.node = BoundedIntegerVariable(0, len(atoms) + len(connectives))
        self.depth = depth

        # node values:
        # 0 for null
        # [1, len(atoms)] for atoms
        # [len(atoms) + 1, len(atoms) + len(connectives)] for connectives

        if depth == 0:
            self.subformulas: Tuple[ModalFormulaTemplate, ...] = ()
        else:
            max_arity = 0 if len(connectives) == 0 else max(connective.get_arity() for connective in connectives)
            self.subformulas = tuple(
                ModalFormulaTemplate(atoms, connectives, depth - 1)
                for _ in range(max_arity)
            )

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
        return connective.construct(*(subformula.get_from_smt_model(model) for subformula in self.subformulas[:arity]))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if isinstance(value, Atom):
            if value in self.atoms:
                return self.node.equals(self.atoms.index(value) + 1)
            else:
                return smt.FALSE()

        return smt.Or(
            smt.And(
                self.node.equals(idx + len(self.atoms) + 1), # node value matches
                connective.construct(*self.subformulas[:connective.get_arity()]).equals(value) # subtrees match
            )
            for idx, connective in enumerate(self.connectives)
            if self.depth != 0 or connective.get_arity() == 0
        )

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        interp = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value == 0:
                continue

            if node_value <= len(self.atoms):
                interp = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        self.atoms[node_value - 1].interpret(frame, valuation, world),
                    ),
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
                interp = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        connective.construct(*self.subformulas[:arity]).interpret(frame, valuation, world),
                    ),
                    interp,
                )
                
        return interp

    def enumerate(self) -> Generator[Formula, None, None]:
        """
        Maybe merge this with FOLUtils.get_ground_terms_in_language
        """

        # depth 0: atoms and 0-ary connectives
        # depth 1: non-0-ary connectives applied to depth 0 terms
        # depth 2: non-0-ary connectives applied to depth 1 and 0 terms (at least one of the argument has to be depth 1)

        # formula of each depth
        depth_map: Dict[int, List[Formula]] = {}

        for depth in range(self.depth + 1):
            if depth == 0:
                depth_map[0] = list(self.atoms) + [ conn.construct() for conn in self.connectives if conn.get_arity() == 0 ]

                for formula in depth_map[0]:
                    yield formula

            else:
                # for each n-ary connective,
                # iterate through all possible combinations of
                # the depths of its subformulas
                # e.g. for a binary connective at depth 2
                # the subformulas could have depths
                # (0, 1), (1, 0), (1, 1)
                # no (0, 0) since that would result in a depth-1 formula

                depth_map[depth] = []

                for conn in self.connectives:
                    if conn.get_arity() == 0:
                        continue

                    for subformula_depths in itertools.product(tuple(range(0, depth)), repeat=conn.get_arity()):
                        # skip depth combinations that would result in a < depth formula
                        if depth - 1 not in subformula_depths:
                            continue

                        subformulas = [ depth_map[subformula_depth] for subformula_depth in subformula_depths ]

                        # now iterate through all formulas of the said depth
                        for subformulas in itertools.product(*(
                            depth_map[subformula_depth] for subformula_depth in subformula_depths
                        )):
                            formula = conn.construct(*subformulas)
                            depth_map[depth].append(formula)
                            yield formula
