from __future__ import annotations

from typing import Tuple, Iterable, Optional
from dataclasses import dataclass

from .language import BaseAST, RelationSymbol
from .syntax import *


class Sentence(BaseAST): ...


@dataclass(frozen=True)
class FixpointDefinition(Sentence):
    relation_symbol: RelationSymbol
    variables: Tuple[Variable, ...]
    definition: Formula

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
    sentences: Tuple[Sentence, ...]

    def extend_axioms(self, axioms: Iterable[Formula]) -> Theory:
        return Theory(
            self.language,
            self.sentences + tuple(map(Axiom, axioms)),
        )

    def find_fixpoint_definition(self, relation_symbol: RelationSymbol) -> Optional[FixpointDefinition]:
        for sentence in self.sentences:
            if isinstance(sentence, FixpointDefinition) and \
               sentence.relation_symbol == relation_symbol:
                return sentence

        return None

    def remove_fixpoint_definition(self, name: str) -> Theory:
        """
        Remove a fixpoint definition from the theory
        """
        sentences = tuple(
            sentence
            for sentence in self.sentences
            if not isinstance(sentence, FixpointDefinition) or sentence.relation_symbol.name != name
        )

        return Theory(self.language, sentences)
