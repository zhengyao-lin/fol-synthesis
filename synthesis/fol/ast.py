"""
AST for many-sorted first order logic with equality
"""

from __future__ import annotations

from typing import Tuple, Any, Union, Optional, Callable, Mapping, Set
from dataclasses import dataclass
from abc import ABC, abstractmethod

from synthesis import smt


class BaseAST:
    ...


@dataclass(frozen=True)
class Sort(BaseAST):
    name: str
    smt_hook: Optional[smt.SMTSort] = None

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class FunctionSymbol(BaseAST):
    input_sorts: Tuple[Sort, ...]
    output_sort: Sort
    name: str
    smt_hook: Optional[Callable[..., smt.SMTTerm]] = None # if set, the function is interpreted as an SMT function


@dataclass(frozen=True)
class RelationSymbol(BaseAST):
    input_sorts: Tuple[Sort, ...]
    name: str
    smt_hook: Optional[Callable[..., smt.SMTTerm]] = None # if set, the function is interpreted as an SMT function


class Term(BaseAST, ABC):
    @abstractmethod
    def substitute(self, substitution: Mapping[Variable, Term]) -> Term: ...

    @abstractmethod
    def get_free_variables(self) -> Set[Variable]: ...


@dataclass(frozen=True)
class Variable(Term):
    name: str
    sort: Sort

    def __str__(self) -> str:
        return f"{self.name}:{self.sort}"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Term:
        if self in substitution:
            return substitution[self]
        return self

    def get_free_variables(self) -> Set[Variable]:
        return { self }


# @dataclass
# class UnsortedVariable(Term):
#     """
#     A temporary construct for parsing
#     """
#     name: str


@dataclass(frozen=True)
class Application(Term):
    function_symbol: FunctionSymbol
    arguments: Tuple[Term, ...]

    def __str__(self) -> str:
        if len(self.arguments) == 0: return self.function_symbol.name
        argument_string = ", ".join((str(arg) for arg in self.arguments))
        return f"{self.function_symbol.name}({argument_string})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Term:
        return Application(self.function_symbol, tuple(argument.substitute(substitution) for argument in self.arguments))

    def get_free_variables(self) -> Set[Variable]:
        free_vars = set()
        for argument in self.arguments:
            free_vars.update(argument.get_free_variables())
        return free_vars


class Formula(BaseAST, ABC):
    @abstractmethod
    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula: ...

    @abstractmethod
    def get_free_variables(self) -> Set[Variable]: ...


class Verum(Formula):
    def __str__(self) -> str:
        return "⊤"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return self

    def get_free_variables(self) -> Set[Variable]:
        return set()


class Falsum(Formula):
    def __str__(self) -> str:
        return "⊥"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return self

    def get_free_variables(self) -> Set[Variable]:
        return set()


# @dataclass(frozen=True)
# class Equality(Formula):
#     left: Term
#     right: Term


@dataclass(frozen=True)
class RelationApplication(Formula):
    relation_symbol: RelationSymbol
    arguments: Tuple[Term, ...]

    def __str__(self) -> str:
        argument_string = ", ".join((str(arg) for arg in self.arguments))
        return f"{self.relation_symbol.name}({argument_string})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return RelationApplication(self.relation_symbol, tuple(argument.substitute(substitution) for argument in self.arguments))

    def get_free_variables(self) -> Set[Variable]:
        free_vars = set()
        for argument in self.arguments:
            free_vars.update(argument.get_free_variables())
        return free_vars


AtomicFormula = Union[Verum, Falsum, RelationApplication]


@dataclass(frozen=True)
class Conjunction(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} /\\ {self.right})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Conjunction(
            self.left.substitute(substitution),
            self.right.substitute(substitution),
        )

    def get_free_variables(self) -> Set[Variable]:
        return self.left.get_free_variables().union(self.right.get_free_variables())


@dataclass(frozen=True)
class Disjunction(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} \\/ {self.right})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Disjunction(
            self.left.substitute(substitution),
            self.right.substitute(substitution),
        )

    def get_free_variables(self) -> Set[Variable]:
        return self.left.get_free_variables().union(self.right.get_free_variables())


@dataclass(frozen=True)
class Negation(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"not {self.formula}"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Negation(self.formula.substitute(substitution))

    def get_free_variables(self) -> Set[Variable]:
        return self.formula.get_free_variables()


@dataclass(frozen=True)
class Implication(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} -> {self.right})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Implication(
            self.left.substitute(substitution),
            self.right.substitute(substitution),
        )

    def get_free_variables(self) -> Set[Variable]:
        return self.left.get_free_variables().union(self.right.get_free_variables())


@dataclass(frozen=True)
class Equivalence(Formula):
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} <-> {self.right})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Equivalence(
            self.left.substitute(substitution),
            self.right.substitute(substitution),
        )

    def get_free_variables(self) -> Set[Variable]:
        return self.left.get_free_variables().union(self.right.get_free_variables())


@dataclass(frozen=True)
class UniversalQuantification(Formula):
    variable: Variable
    body: Formula

    def __str__(self) -> str:
        return f"(forall {self.variable}. {self.body})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        if self.variable in substitution:
            substitution = { k: v for k, v in substitution.items() if k != self.variable }
        return UniversalQuantification(self.variable, self.body.substitute(substitution))

    def get_free_variables(self) -> Set[Variable]:
        return self.body.get_free_variables().difference({ self.variable })


@dataclass(frozen=True)
class ExistentialQuantification(Formula):
    variable: Variable
    body: Formula

    def __str__(self) -> str:
        return f"(exists {self.variable}. {self.body})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        if self.variable in substitution:
            substitution = { k: v for k, v in substitution.items() if k != self.variable }
        return ExistentialQuantification(self.variable, self.body.substitute(substitution))

    def get_free_variables(self) -> Set[Variable]:
        return self.body.get_free_variables().difference({ self.variable })


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

        elif isinstance(formula, Conjunction):
            return Conjunction(
                self.unfold_in_formula(formula.left),
                self.unfold_in_formula(formula.right),
            )

        elif isinstance(formula, Disjunction):
            return Disjunction(
                self.unfold_in_formula(formula.left),
                self.unfold_in_formula(formula.right),
            )

        elif isinstance(formula, Implication):
            return Implication(
                self.unfold_in_formula(formula.left),
                self.unfold_in_formula(formula.right),
            )

        elif isinstance(formula, Equivalence):
            return Equivalence(
                self.unfold_in_formula(formula.left),
                self.unfold_in_formula(formula.right),
            )

        elif isinstance(formula, UniversalQuantification):
            return UniversalQuantification(
                formula.variable,
                self.unfold_in_formula(formula.body),
            )

        elif isinstance(formula, ExistentialQuantification):
            return ExistentialQuantification(
                formula.variable,
                self.unfold_in_formula(formula.body),
            )

        assert False, f"unable to unfold fixpoint definition in {formula}"


@dataclass(frozen=True)
class Axiom(Sentence):
    formula: Formula


@dataclass(frozen=True)
class Language:
    """
    A many-sorted language
    """
    sorts: Tuple[Sort, ...]
    function_symbols: Tuple[FunctionSymbol, ...]
    relation_symbols: Tuple[RelationSymbol, ...]

    def get_max_function_arity(self) -> int:
        return max(tuple(len(symbol.input_sorts) for symbol in self.function_symbols) + (0,))

    def get_max_relation_arity(self) -> int:
        return max(tuple(len(symbol.input_sorts) for symbol in self.relation_symbols) + (0,))

    def expand(self, other: Language) -> Language:
        for sort in other.sorts:
            assert sort not in self.sorts, f"duplicate sort {sort}"

        for function_symbol in other.function_symbols:
            assert function_symbol not in self.function_symbols, f"duplicate function symbol {function_symbol}"

        for relation_symbol in other.relation_symbols:
            assert relation_symbol not in self.relation_symbols, f"duplicate relation symbol {relation_symbol}"

        return Language(
            self.sorts + other.sorts,
            self.function_symbols + other.function_symbols,
            self.relation_symbols + other.relation_symbols,
        )


@dataclass
class Theory:
    language: Language
    sentences: Tuple[Sentence, ...]
