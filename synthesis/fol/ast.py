"""
AST for many-sorted first order logic with equality
"""

from __future__ import annotations

from typing import Tuple, Any
from dataclasses import dataclass


class BaseAST:
    ...


@dataclass(frozen=True)
class Sort(BaseAST):
    name: str

    def __str__(self) -> str:
        return self.name


class UninterpretedSort(Sort): ...


class SMTSort(Sort): ...


@dataclass(frozen=True)
class FunctionSymbol(BaseAST):
    input_sorts: Tuple[Sort, ...]
    output_sort: Sort
    name: str


@dataclass(frozen=True)
class RelationSymbol(BaseAST):
    input_sorts: Tuple[Sort, ...]
    name: str


class Term(BaseAST):
    ...


@dataclass(frozen=True)
class Variable(Term):
    name: str
    sort: Sort

    def __str__(self) -> str:
        return f"{self.name}:{self.sort}"


@dataclass
class UnsortedVariable(Term):
    """
    A temporary construct for parsing
    """
    name: str
    


@dataclass(frozen=True)
class Application(Term):
    function_symbol: FunctionSymbol
    arguments: Tuple[Term, ...]

    def __str__(self) -> str:
        argument_string = ", ".join((str(arg) for arg in self.arguments))
        return f"{self.function_symbol.name}({argument_string})"


class Formula(BaseAST):
    ...


class Verum(Formula):
    ...


class Falsum(Formula):
    ...


@dataclass(frozen=True)
class Equality(Formula):
    left: Term
    right: Term


@dataclass(frozen=True)
class RelationApplication(Formula):
    relation_symbol: RelationSymbol
    arguments: Tuple[Term, ...]


@dataclass(frozen=True)
class Conjunction(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Disjunction(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Negation(Formula):
    formula: Formula


@dataclass(frozen=True)
class Implication(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True)
class Equivalence(Formula):
    left: Formula
    right: Formula
    lfp: bool = False


@dataclass(frozen=True)
class UniversalQuantification(Formula):
    variable: Variable
    body: Formula


@dataclass(frozen=True)
class ExistentialQuantification(Formula):
    variable: Variable
    body: Formula


@dataclass(frozen=True)
class Language:
    """
    A many-sorted language
    """
    sorts: Tuple[Sort, ...]
    function_symbols: Tuple[FunctionSymbol, ...]
    relation_symbols: Tuple[RelationSymbol, ...]

    def get_max_function_arity(self) -> int:
        return max(tuple(len(symbol.input_sorts) for symbol in self.function_symbols))
