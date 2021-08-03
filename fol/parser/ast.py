"""
Extending the syntax tree of FOL to include some temporary parsing constructs
"""

from typing import Tuple, Mapping, Optional, TypeVar, Generic

from fol.base.syntax import *
from fol.base.theory import *


_T = TypeVar("_T")


@dataclass(frozen=True)
class Attribute:
    name: str
    arguments: Tuple[str, ...]


class UnresolvedAST(Generic[_T]):
    def substitute(self, substitution: Mapping[Variable, Term]) -> _T:
        raise NotImplementedError()

    def get_free_variables(self) -> Set[Variable]:
        raise NotImplementedError()

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        raise NotImplementedError()

    def get_from_smt_model(self, model: smt.SMTModel) -> _T:
        raise NotImplementedError()

    def get_constraint(self) -> smt.SMTTerm:
        raise NotImplementedError()


@dataclass(frozen=True)
class UnresolvedVariable(UnresolvedAST[Term], Term):
    name: str
    sort: Optional[str] = None


@dataclass(frozen=True)
class UnresolvedApplication(UnresolvedAST[Term], Term):
    name: str
    arguments: Tuple[Term, ...]


@dataclass(frozen=True)
class UnresolvedRelationApplication(UnresolvedAST[Formula], Formula):
    name: str
    arguments: Tuple[Term, ...]


@dataclass(frozen=True)
class UnresolvedUniversalQuantification(UnresolvedAST[Formula], Formula):
    variable: UnresolvedVariable
    body: Formula


@dataclass(frozen=True)
class UnresolvedExistentialQuantification(UnresolvedAST[Formula], Formula):
    variable: UnresolvedVariable
    body: Formula


@dataclass(frozen=True)
class UnresolvedSortDefinition(Sentence):
    sort: Sort
    attributes: Tuple[Attribute, ...]


@dataclass(frozen=True)
class UnresolvedFunctionDefinition(Sentence):
    name: str
    input_sorts: Tuple[str, ...]
    output_sort: str
    attributes: Tuple[Attribute, ...]


@dataclass(frozen=True)
class UnresolvedRelationDefinition(Sentence):
    name: str
    input_sorts: Tuple[str, ...]
    attributes: Tuple[Attribute, ...]


@dataclass(frozen=True)
class UnresolvedFixpointDefinition(Sentence):
    name: str
    variables: Tuple[UnresolvedVariable, ...]
    definition: Formula


@dataclass(frozen=True)
class UnresolvedTheory(BaseAST):
    name: str
    sentences: Tuple[Sentence, ...]
