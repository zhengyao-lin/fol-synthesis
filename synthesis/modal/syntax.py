from __future__ import annotations

from typing import Mapping, Set, Tuple
from dataclasses import dataclass
from abc import ABC, abstractmethod, abstractstaticmethod

from synthesis.smt import smt
from synthesis.template import Template

from .semantics import Frame


Interpretation = Tuple[smt.SMTVariable, smt.SMTTerm] # (world, truth on the world)


class Formula(Template["Formula"], ABC):
    @abstractmethod
    def get_atoms(self) -> Set[Atom]: ...

    @abstractmethod
    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm: ...

    def interpret_on_all_worlds(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction]) -> smt.SMTTerm:
        var = frame.get_fresh_constant()
        return frame.universally_quantify(var, self.interpret(frame, valuation, var))


@dataclass
class Falsum(Formula):
    def __str__(self) -> str:
        return "⊥"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.FALSE()

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return self

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.Bool(self == value)

    def get_atoms(self) -> Set[Atom]:
        return set()


@dataclass
class Verum(Formula):
    def __str__(self) -> str:
        return "⊤"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.TRUE()
    
    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return self

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.Bool(self == value)

    def get_atoms(self) -> Set[Atom]:
        return set()


@dataclass(frozen=True)
class Atom(Formula):
    name: str

    def __str__(self) -> str:
        return self.name

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return valuation[self](world)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return self

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.Bool(self == value)

    def get_atoms(self) -> Set[Atom]:
        return { self }


@dataclass(frozen=True)
class Conjunction(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} /\\ {self.right})"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.And(
            self.left.interpret(frame, valuation, world),
            self.right.interpret(frame, valuation, world),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.left.get_constraint(),
            self.right.get_constraint(),
        )

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Conjunction(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Conjunction):
            return smt.FALSE()

        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )

    def get_atoms(self) -> Set[Atom]:
        return self.left.get_atoms().union(self.right.get_atoms())


@dataclass(frozen=True)
class Disjunction(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} \\/ {self.right})"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Or(
            self.left.interpret(frame, valuation, world),
            self.right.interpret(frame, valuation, world),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.left.get_constraint(),
            self.right.get_constraint(),
        )

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Disjunction(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Disjunction):
            return smt.FALSE()

        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )

    def get_atoms(self) -> Set[Atom]:
        return self.left.get_atoms().union(self.right.get_atoms())


@dataclass(frozen=True)
class Implication(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} -> {self.right})"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Implies(
            self.left.interpret(frame, valuation, world),
            self.right.interpret(frame, valuation, world),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.left.get_constraint(),
            self.right.get_constraint(),
        )

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Implication(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Implication):
            return smt.FALSE()

        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )

    def get_atoms(self) -> Set[Atom]:
        return self.left.get_atoms().union(self.right.get_atoms())


@dataclass(frozen=True)
class Equivalence(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} <-> {self.right})"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Iff(
            self.left.interpret(frame, valuation, world),
            self.right.interpret(frame, valuation, world),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.left.get_constraint(),
            self.right.get_constraint(),
        )

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Equivalence(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Equivalence):
            return smt.FALSE()

        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )

    def get_atoms(self) -> Set[Atom]:
        return self.left.get_atoms().union(self.right.get_atoms())


@dataclass(frozen=True)
class Negation(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"¬{self.formula}"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Not(self.formula.interpret(frame, valuation, world))

    def get_constraint(self) -> smt.SMTTerm:
        return self.formula.get_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Negation(self.formula.get_from_smt_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Negation):
            return smt.FALSE()
        return self.formula.equals(value.formula)

    def get_atoms(self) -> Set[Atom]:
        return self.formula.get_atoms()


@dataclass(frozen=True)
class Box(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"□{self.formula}"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        var = frame.get_fresh_constant()

        # i.e. for all successors of the current world, self.formula holds
        return frame.universally_quantify(
            var,
            smt.Implies(
                frame.interpret_transition(world, var),
                self.formula.interpret(frame, valuation, var),
            ),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return self.formula.get_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Box(self.formula.get_from_smt_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Box):
            return smt.FALSE()
        return self.formula.equals(value.formula)

    def get_atoms(self) -> Set[Atom]:
        return self.formula.get_atoms()


@dataclass(frozen=True)
class Diamond(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"◊{self.formula}"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        var = frame.get_fresh_constant()

        # i.e. exists a successor of the current world in which self.formula holds
        return frame.existentially_quantify(
            var,
            smt.And(
                frame.interpret_transition(world, var),
                self.formula.interpret(frame, valuation, var),
            ),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return self.formula.get_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Diamond(self.formula.get_from_smt_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Diamond):
            return smt.FALSE()
        return self.formula.equals(value.formula)

    def get_atoms(self) -> Set[Atom]:
        return self.formula.get_atoms()


@dataclass(frozen=True)
class BoxPast(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"□ₚ{self.formula}"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        var = frame.get_fresh_constant()

        # i.e. for all successors of the current world, self.formula holds
        return frame.universally_quantify(
            var,
            smt.Implies(
                frame.interpret_transition(var, world),
                self.formula.interpret(frame, valuation, var),
            ),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return self.formula.get_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return BoxPast(self.formula.get_from_smt_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, BoxPast):
            return smt.FALSE()
        return self.formula.equals(value.formula)

    def get_atoms(self) -> Set[Atom]:
        return self.formula.get_atoms()


@dataclass(frozen=True)
class DiamondPast(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"◊ₚ{self.formula}"

    def interpret(self, frame: Frame, valuation: Mapping[Atom, smt.SMTFunction], world: smt.SMTTerm) -> smt.SMTTerm:
        var = frame.get_fresh_constant()

        # i.e. exists a successor of the current world in which self.formula holds
        return frame.existentially_quantify(
            var,
            smt.And(
                frame.interpret_transition(var, world),
                self.formula.interpret(frame, valuation, var),
            ),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return self.formula.get_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return DiamondPast(self.formula.get_from_smt_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, DiamondPast):
            return smt.FALSE()
        return self.formula.equals(value.formula)

    def get_atoms(self) -> Set[Atom]:
        return self.formula.get_atoms()
