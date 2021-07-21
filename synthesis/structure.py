from typing import Tuple, Dict, Callable

from dataclasses import dataclass
from abc import ABC, abstractmethod

from .fol.ast import *
from . import smt


class CarrierSet(ABC):
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
    def interpret_relation(self, symbol: FunctionSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm: ...


@dataclass
class RefinementCarrierSet(CarrierSet):
    """
    A builtin sort refined by a predicate
    """

    sort: smt.SMTSort
    predicate: Callable[[smt.SMTTerm], smt.SMTTerm] = lambda _: smt.TRUE()

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.ForAll((variable,), smt.Implies(self.predicate(variable), formula))

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Exists((variable,), smt.And(self.predicate(variable), formula))
    
    @abstractmethod
    def get_fresh_constant(self, solver: smt.SMTSolver, sort: Sort) -> smt.SMTVariable:
        var = smt.FreshSymbol(self.sort)
        solver.add_assertion(self.predicate(var))
        return var


@dataclass
class FiniteCarrierSet(CarrierSet):
    sort: smt.SMTSort
    collection: Tuple[smt.SMTTerm, ...]

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.And(*(formula.substitute({ variable: element }) for element in self.collection))

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        return smt.Or(*(formula.substitute({ variable: element }) for element in self.collection))
    
    @abstractmethod
    def get_fresh_constant(self, solver: smt.SMTSolver, sort: Sort) -> smt.SMTVariable:
        var = smt.FreshSymbol(self.sort)
        solver.add_assertion(smt.Or(*(smt.Equals(var, element) for element in self.collection)))
        return var


@dataclass
class SymbolicStructure(Structure):
    language: Language
    carriers: Dict[Sort, CarrierSet]
    function_interpretations: Dict[FunctionSymbol, Callable[..., smt.SMTTerm]]
    relation_interpretations: Dict[FunctionSymbol, Callable[..., smt.SMTTerm]]

    def interpret_sort(self, sort: Sort) -> CarrierSet:
        return self.carriers[sort]

    def interpret_function(self, symbol: FunctionSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm:
        return self.function_interpretations[symbol](*arguments)

    def interpret_relation(self, symbol: FunctionSymbol, *arguments: smt.SMTTerm) -> smt.SMTTerm:
        return self.relation_interpretations[symbol](*arguments)
