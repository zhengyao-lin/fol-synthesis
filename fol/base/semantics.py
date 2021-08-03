"""
Structure of a many-sorted language
"""

from typing import Tuple, Mapping

from dataclasses import dataclass
from abc import ABC, abstractmethod

from fol.smt import smt

from .language import Sort, FunctionSymbol, RelationSymbol, Language


class CarrierSet(ABC):
    @abstractmethod
    def get_smt_sort(self) -> smt.SMTSort: ...

    @abstractmethod
    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...

    @abstractmethod
    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...
    
    @abstractmethod
    def get_fresh_constant(self, solver: smt.SMTSolver, sort: Sort) -> smt.SMTVariable: ...


class Structure(ABC):
    """
    NOTE: a structure is binded to a smt solver context

    Structure of a many-sorted language
    """

    @abstractmethod
    def interpret_sort(self, sort: Sort) -> CarrierSet: ...

    @abstractmethod
    def interpret_function(self, symbol: FunctionSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm: ...

    @abstractmethod
    def interpret_relation(self, symbol: RelationSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm: ...

    def get_smt_sort(self, sort: Sort) -> smt.SMTSort:
        return self.interpret_sort(sort).get_smt_sort()


@dataclass
class RefinementCarrierSet(CarrierSet):
    """
    A builtin sort refined by a predicate
    """

    sort: smt.SMTSort
    predicate: smt.SMTFunction = lambda _: smt.TRUE()

    def get_smt_sort(self) -> smt.SMTSort:
        return self.sort

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.ForAll((variable,), smt.Implies(self.predicate(variable), formula))

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Exists((variable,), smt.And(self.predicate(variable), formula))
    
    def get_fresh_constant(self, solver: smt.SMTSolver, sort: Sort) -> smt.SMTVariable:
        var = smt.FreshSymbol(self.sort)
        solver.add_assertion(self.predicate(var))
        return var


@dataclass
class FiniteCarrierSet(CarrierSet):
    sort: smt.SMTSort
    domain: Tuple[smt.SMTTerm, ...]

    def get_smt_sort(self) -> smt.SMTSort:
        return self.sort

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.And(*(formula.substitute({ variable: element }) for element in self.domain))

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Or(*(formula.substitute({ variable: element }) for element in self.domain))
    
    def get_fresh_constant(self, solver: smt.SMTSolver, sort: Sort) -> smt.SMTVariable:
        var = smt.FreshSymbol(self.sort)
        solver.add_assertion(smt.Or(*(smt.Equals(var, element) for element in self.domain)))
        return var


class SymbolicStructure(Structure):
    def __init__(
        self,
        language: Language,
        carriers: Mapping[Sort, CarrierSet],
        function_interpretations: Mapping[FunctionSymbol, smt.SMTFunction],
        relation_interpretations: Mapping[RelationSymbol, smt.SMTFunction],
    ):
        self.language = language
        self.carriers = dict(carriers)
        self.function_interpretations = dict(function_interpretations)
        self.relation_interpretations = dict(relation_interpretations)

    def interpret_sort(self, sort: Sort) -> CarrierSet:
        if sort not in self.carriers:
            assert sort.smt_hook is not None, f"unable to interpret sort {sort}"
            return RefinementCarrierSet(sort.smt_hook)

        return self.carriers[sort]

    def interpret_function(self, symbol: FunctionSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm:
        if symbol not in self.function_interpretations:
            assert symbol.smt_hook is not None, f"unable to interpret function symbol {symbol}"
            return symbol.smt_hook(*arguments)

        return self.function_interpretations[symbol](*arguments)

    def interpret_relation(self, symbol: RelationSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm:
        if symbol not in self.relation_interpretations:
            assert symbol.smt_hook is not None, f"unable to interpret relation symbol {symbol}"
            return symbol.smt_hook(*arguments)

        return self.relation_interpretations[symbol](*arguments)
