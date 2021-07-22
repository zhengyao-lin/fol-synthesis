from typing import Tuple, Dict, Mapping

from dataclasses import dataclass
from abc import ABC, abstractmethod

from .fol.ast import *
from . import smt


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

    def interpret_term(self, term: Term, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        if isinstance(term, Variable):
            assert term in valuation, f"variable {term} not provided in the valuation {valuation}"
            return valuation[term]

        elif isinstance(term, Application):
            arguments = (self.interpret_term(argument, valuation) for argument in term.arguments)
            return self.interpret_function(term.function_symbol, *arguments)

        assert False, f"unable to interpret {term}"

    def interpret_formula(self, formula: Formula, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        if isinstance(formula, Verum):
            return smt.TRUE()

        elif isinstance(formula, Falsum):
            return smt.FALSE()

        elif isinstance(formula, RelationApplication):
            arguments = (self.interpret_term(argument, valuation) for argument in formula.arguments) 
            return self.interpret_relation(formula.relation_symbol, *arguments)

        elif isinstance(formula, Negation):
            return smt.Not(self.interpret_formula(formula.formula, valuation))

        elif isinstance(formula, Conjunction):
            return smt.And(self.interpret_formula(formula.left, valuation), self.interpret_formula(formula.right, valuation))

        elif isinstance(formula, Disjunction):
            return smt.Or(self.interpret_formula(formula.left, valuation), self.interpret_formula(formula.right, valuation))

        elif isinstance(formula, Implication):
            return smt.Implies(self.interpret_formula(formula.left, valuation), self.interpret_formula(formula.right, valuation))

        elif isinstance(formula, Equivalence):
            return smt.Iff(self.interpret_formula(formula.left, valuation), self.interpret_formula(formula.right, valuation))

        elif isinstance(formula, UniversalQuantification):
            carrier = self.interpret_sort(formula.variable.sort)
            smt_var = smt.FreshSymbol(carrier.get_smt_sort())
            body = self.interpret_formula(formula.body, { **valuation, formula.variable: smt_var })
            return carrier.universally_quantify(smt_var, body)

        elif isinstance(formula, ExistentialQuantification):
            carrier = self.interpret_sort(formula.variable.sort)
            smt_var = smt.FreshSymbol(carrier.get_smt_sort())
            body = self.interpret_formula(formula.body, { **valuation, formula.variable: smt_var })
            return carrier.existentially_quantify(smt_var, body)

        assert False, f"unable to interpret {formula}"


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
