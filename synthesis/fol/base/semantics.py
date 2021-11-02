"""
Structure of a many-sorted language
"""

from typing import Tuple, Mapping, List, Union, Callable

from dataclasses import dataclass
from abc import ABC, abstractmethod

import itertools

from synthesis.smt import smt

from .language import Sort, FunctionSymbol, RelationSymbol, Language


class CarrierSet(ABC):
    @abstractmethod
    def get_smt_sort(self) -> smt.SMTSort: ...

    @abstractmethod
    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...

    @abstractmethod
    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...
    
    @abstractmethod
    def get_fresh_constant(self, solver: smt.SMTSolver) -> smt.SMTVariable: ...

    def __str__(self) -> str:
        raise NotImplementedError()


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

    def get_fresh_function(self, solver: smt.SMTSolver, symbol: FunctionSymbol) -> smt.SMTFunction:
        assert symbol.smt_hook is None

        if len(symbol.input_sorts) == 0:
            constant = self.interpret_sort(symbol.output_sort).get_fresh_constant(solver)
            return lambda: constant

        input_smt_sorts = tuple(self.interpret_sort(sort).get_smt_sort() for sort in symbol.input_sorts)

        output_carrier = self.interpret_sort(symbol.output_sort)
        output_smt_sort = output_carrier.get_smt_sort()

        smt_function = smt.FreshFunction(input_smt_sorts, output_smt_sort)

        # if we have no refinemenet, there is no need to add any constraint
        if isinstance(output_carrier, RefinementCarrierSet) and \
           output_carrier.predicate(smt.FreshSymbol(output_smt_sort)).is_true():
            return smt_function

        # add constraint that the function is in-range
        fresh_inputs = tuple(smt.FreshSymbol(sort) for sort in input_smt_sorts)
        fresh_output = smt.FreshSymbol(output_smt_sort)

        # forall inputs, exists output, output = f(inputs)
        constraint = output_carrier.existentially_quantify(fresh_output, smt.Equals(fresh_output, smt_function(*fresh_inputs)))

        for fresh_input, sort in zip(fresh_inputs, symbol.input_sorts):
            constraint = self.interpret_sort(sort).universally_quantify(fresh_input, constraint)

        # NOTE: this may introduce quantified SMT formulas
        solver.add_assertion(constraint)

        return smt_function


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
    
    def get_fresh_constant(self, solver: smt.SMTSolver) -> smt.SMTVariable:
        var = smt.FreshSymbol(self.sort)
        solver.add_assertion(self.predicate(var))
        return var

    def __str__(self) -> str:
        fresh = smt.FreshSymbol(self.sort)
        return f"{{ {fresh}: {self.sort} | {self.predicate(fresh)} }}"


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
    
    def get_fresh_constant(self, solver: smt.SMTSolver) -> smt.SMTVariable:
        var = smt.FreshSymbol(self.sort)
        solver.add_assertion(smt.Or(*(smt.Equals(var, element) for element in self.domain)))
        return var

    def __str__(self) -> str:
        return f"{{ {', '.join(map(str, self.domain))} }}"


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
            return RefinementCarrierSet(sort.smt_hook, sort.smt_hook_constraint or (lambda _: smt.TRUE()))

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

    def get_domain_of_sorts(self, sorts: Tuple[Sort, ...]) -> Tuple[Tuple[smt.SMTTerm, ...], ...]:
        """
        Generate all elements in the domain of the product of the given sorts
        Any potentially infinite sort is represented by a fresh symbol
        """

        domains: List[Tuple[smt.SMTTerm, ...]] = []

        for sort in sorts:
            carrier = self.interpret_sort(sort)

            if isinstance(carrier, FiniteCarrierSet):
                domains.append(carrier.domain)
            elif isinstance(carrier, RefinementCarrierSet):
                domains.append((smt.FreshSymbol(carrier.get_smt_sort()),))
            else:
                assert False, f"unsupported carrier set {carrier}"

        return tuple(domains)

    def __str__(self) -> str:
        """
        Stringify the finitary part of the structure
        """

        output: List[str] = []

        domain_to_str: Callable[[Tuple[smt.SMTTerm, ...]], str] = \
            lambda terms: f"({', '.join(map(str, terms))})" if len(terms) != 1 else str(terms[0])

        for sort, carrier in self.carriers.items():
            output.append(f"{sort} := {carrier}")

        for function_symbol, interp in self.function_interpretations.items():
            output.append(f"{function_symbol} :=")

            if len(function_symbol.input_sorts) == 0:
                output[-1] += f" {interp()}"
            else:
                for elems in itertools.product(*self.get_domain_of_sorts(function_symbol.input_sorts)):
                    value = interp(*elems).simplify()
                    output.append(f"    {domain_to_str(elems)} |-> {value}")

        for relation_symbol, interp in self.relation_interpretations.items():
            output.append(f"{relation_symbol} := {{")
            non_empty = False

            for elems in itertools.product(*self.get_domain_of_sorts(relation_symbol.input_sorts)):
                value = interp(*elems).simplify()

                if value.is_true():
                    non_empty = True
                    output.append(f"    {domain_to_str(elems)}")

                elif not value.is_false():
                    non_empty = True
                    output.append(f"    {domain_to_str(elems)} if {value}")

            if not non_empty:
                output[-1] += "}"
            else:
                output.append("}")

        return "\n".join(output)

    def get_free_finite_relation(self, input_sorts: Tuple[Sort, ...]) -> Tuple[smt.SMTFunction, Tuple[smt.SMTVariable, ...]]:
        """
        Generate a free finite relation with the given input sorts on the structure,
        represented by a list of boolean variables.
        All input sorts have to be interpreted as a finite set in the current structure.

        Return an SMT function and variable associated to the relation (so that it can be universally quantified)
        """

        domains: List[Tuple[smt.SMTTerm, ...]] = []
        switches: List[smt.SMTFunction] = []
        control_vars: List[smt.SMTVariable] = []

        for sort in input_sorts:
            carrier = self.interpret_sort(sort)
            assert isinstance(carrier, FiniteCarrierSet), \
                   f"sort {sort} is not finite"
            domains.append(carrier.domain)

        for arguments in itertools.product(*domains):
            control_var = smt.FreshSymbol(smt.BOOL)
            switches.append((lambda arguments, control_var:
                lambda other: smt.And(
                    *(smt.Equals(left, right) for left, right in zip(arguments, other)),
                    control_var,
                )
            )(arguments, control_var))
            control_vars.append(control_var)
            
        relation = lambda *arguments: smt.Or(switch(arguments) for switch in switches)

        return relation, tuple(control_vars)
