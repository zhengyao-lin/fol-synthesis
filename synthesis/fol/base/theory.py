from __future__ import annotations

from typing import Tuple, Iterable, Optional, Dict
from dataclasses import dataclass

from .language import BaseAST, RelationSymbol
from .syntax import *


class Sentence(BaseAST): ...


@dataclass(frozen=True)
class FixpointDefinition(Sentence):
    relation_symbol: RelationSymbol
    variables: Tuple[Variable, ...]
    definition: Formula
    bound: Optional[int] = None

    def as_formula(self) -> Formula:
        """
        Return a formula describing the fixpoint (not necessarily an LFP)
        """
        formula: Formula = Equivalence(RelationApplication(self.relation_symbol, self.variables), self.definition)

        for var in self.variables[::-1]:
            formula = UniversalQuantification(var, formula)

        return formula

    def unfold_definition(self, n: int) -> FixpointDefinition:
        """
        Create a new definition with itself unfolded n times
        """
        formula = self.definition

        for _ in range(n):
            formula = self.unfold_in_formula(formula)

        return FixpointDefinition(
            self.relation_symbol,
            self.variables,
            formula,
        )

    def unfold_in_formula(self, formula: Formula) -> Formula:
        """
        Replace application of self.relation_symbol in a given formula with the definition
        """

        if isinstance(formula, Verum) or isinstance(formula, Falsum):
            return formula

        elif isinstance(formula, RelationApplication):
            if formula.relation_symbol == self.relation_symbol:
                substitution = { k: v for k, v in zip(self.variables, formula.arguments) }
                return self.definition.substitute(substitution)
            else:
                return formula

        elif isinstance(formula, Equality):
            return formula

        elif isinstance(formula, Negation):
            return Negation(self.unfold_in_formula(formula.formula))

        elif isinstance(formula, Conjunction) or \
             isinstance(formula, Disjunction) or \
             isinstance(formula, Implication) or \
             isinstance(formula, Equivalence):
            return type(formula)(
                self.unfold_in_formula(formula.left),
                self.unfold_in_formula(formula.right),
            )

        elif isinstance(formula, UniversalQuantification) or \
             isinstance(formula, ExistentialQuantification):
            return type(formula)(
                formula.variable,
                self.unfold_in_formula(formula.body),
            )

        assert False, f"unable to unfold fixpoint definition in {formula}"


@dataclass(frozen=True)
class Axiom(Sentence):
    formula: Formula


@dataclass(frozen=True)
class Theory(BaseAST):
    language: Language
    fixpoint_definitions: Mapping[RelationSymbol, FixpointDefinition]
    axioms: Tuple[Axiom, ...]

    @staticmethod
    def empty_theory(language: Language) -> Theory:
        return Theory(language, {}, ())

    def expand_language(self, expansion: Language) -> Theory:
        return Theory(self.language.expand(expansion), self.fixpoint_definitions, self.axioms)

    def extend_axioms(self, axioms: Iterable[Formula]) -> Theory:
        return Theory(
            self.language,
            self.fixpoint_definitions,
            self.axioms + tuple(map(Axiom, axioms)),
        )

    def combine(self, theory: Theory) -> Theory:
        overlapping_fixpoints = set(self.fixpoint_definitions.keys()).intersection(theory.fixpoint_definitions.keys())
        assert len(overlapping_fixpoints) == 0, \
               f"overlapping fixpoint definitions of {overlapping_fixpoints}"

        return Theory(
            self.language.expand(theory.language),
            { **self.fixpoint_definitions, **theory.fixpoint_definitions },
            self.axioms + theory.axioms,
        )

    def find_fixpoint_definition(self, relation_symbol: RelationSymbol) -> Optional[FixpointDefinition]:
        return self.fixpoint_definitions.get(relation_symbol)

    def remove_fixpoint_definition(self, name: str) -> Theory:
        """
        Remove a fixpoint definition from the theory
        """
        for symbol in self.fixpoint_definitions:
            if symbol.name == name:
                return Theory(
                    self.language,
                    { k: v for k, v in self.fixpoint_definitions.items() if k != symbol },
                    self.axioms,
                )

        return self

    def get_axioms(self) -> Iterable[Axiom]:
        return self.axioms

    def get_fixpoint_definitions(self) -> Iterable[FixpointDefinition]:
        return self.fixpoint_definitions.values()

    def convert_to_fo_theory(self) -> Iterable[Formula]:
        """
        Get a first order abstraction of the theory,
        where fixpoint definitions are converted to
        a first order sentence
        """
        return tuple(axiom.formula for axiom in self.axioms) + \
               tuple(definition.as_formula() for definition in self.fixpoint_definitions.values())

