from typing import Any, Generic, TypeVar, Tuple

from dataclasses import dataclass
from abc import ABC, abstractmethod

from .fol.ast import *
from .structure import CarrierSet, Structure
from . import smt

T = TypeVar("T")


class VariableWithConstraint(Generic[T], ABC):
    def add_to_solver(self, solver: smt.SMTSolver) -> None:
        solver.add_assertion(self.get_constraint())

    @abstractmethod
    def get_constraint(self) -> smt.SMTTerm:
        ...

    @abstractmethod
    def get_from_model(self, model: smt.SMTModel) -> T:
        ...

    @abstractmethod
    def equals(self, value: T) -> smt.SMTTerm:
        ...


class BoundedIntegerVariable(VariableWithConstraint[int]):
    """
    An integer variable with range lower upper
    """

    def __init__(self, lower: int, upper: int):
        assert upper >= lower
        self.lower = lower
        self.upper = upper
        self.num_bits = (upper - lower + 1).bit_length()
        self.variable = smt.FreshSymbol(typename=smt.BVType(self.num_bits))

    def get_constraint(self) -> smt.SMTTerm:
        # TODO
        return smt.TRUE()

    def get_from_model(self, model: smt.SMTModel) -> int:
        return model[self.variable].bv2nat() + self.lower # type: ignore

    def equals(self, value: int) -> smt.SMTTerm:
        return smt.Equals(self.variable, smt.BV(value - self.lower, self.num_bits))


class TermVariable(VariableWithConstraint[Term]):
    """
    Template for a term
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], depth: int):
        self.language = language
        self.free_vars = free_vars
        self.depth = depth
        self.node = BoundedIntegerVariable(0, len(self.free_vars) + len(self.language.function_symbols))

        if depth != 0:
            self.subterms = tuple(TermVariable(language, self.free_vars, depth - 1) for _ in range(language.get_max_function_arity()))
        else:
            self.subterms = ()

    def get_constraint(self) -> smt.SMTTerm:
        """
        The term can be of any sort
        """
        return smt.Or(*(self.get_well_formedness_constraint(sort) for sort in self.language.sorts))

    def get_from_model(self, model: smt.SMTModel) -> Term:
        """
        Get a concrete term from the given model
        """
        node_value = self.node.get_from_model(model)
        assert node_value != 0, f"unexpected node value {node_value}"

        if node_value <= len(self.free_vars):
            return self.free_vars[node_value - 1]
        else:
            symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
            arity = len(symbol.input_sorts)
            return Application(symbol, tuple(subterm.get_from_model(model) for subterm in self.subterms[:arity]))

    def equals(self, value: Term) -> smt.SMTTerm:
        if isinstance(value, Variable):
            var_index = self.free_vars.index(value)
            return self.node.equals(var_index + 1)

        elif isinstance(value, Application):
            symbol_index = self.language.function_symbols.index(value.function_symbol)
            arity = len(value.function_symbol.input_sorts)

            return smt.And(
                self.node.equals(symbol_index + 1 + len(self.free_vars)),
                *(subterm.equals(argument) for argument, subterm in zip(value.arguments, self.subterms[:arity])),
            )

        assert False, f"unknown term {value}"

    def get_is_null_constraint(self) -> smt.SMTTerm:
        """
        Return a constraint saying that the subtree starting at self does not exist
        """
        return smt.And(self.node.equals(0), *(subterm.get_is_null_constraint() for subterm in self.subterms))

    def get_well_formedness_constraint(self, sort: Sort) -> smt.SMTTerm:
        """
        Return a constraint saying that the term is well-formed and has sort <sort> 
        """
        constraint = smt.FALSE()

        for node_value in range(1, len(self.free_vars) + len(self.language.function_symbols) + 1):
            if node_value <= len(self.free_vars):
                variable = self.free_vars[node_value - 1]

                if variable.sort == sort:
                    constraint = smt.Or(
                        smt.And(
                            self.node.equals(node_value),
                            *(subterm.get_is_null_constraint() for subterm in self.subterms),
                        ),
                        constraint,
                    )
            elif self.depth != 0:
                symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]

                if symbol.output_sort == sort:
                    arity = len(symbol.input_sorts)
                    constraint = smt.Or(
                        smt.And(
                            self.node.equals(node_value),
                            # the i-th subterm should have the i-th input sort
                            *(subterm.get_well_formedness_constraint(sort) for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])),
                            *(subterm.get_is_null_constraint() for subterm in self.subterms[arity:]),
                        ),
                        constraint,
                    )

        return constraint


class AtomicFormulaVariable(VariableWithConstraint[AtomicFormula]):
    """
    Template for an atomic formula (i.e. false, true, or other relations)
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], term_depth: int):
        self.language = language
        self.free_vars = free_vars
        self.term_depth = term_depth
        self.node = BoundedIntegerVariable(0, 2 + len(language.relation_symbols))

        self.subterms = tuple(TermVariable(language, free_vars, term_depth) for _ in range(language.get_max_relation_arity()))

    def get_constraint(self) -> smt.SMTTerm:
        return self.get_well_formedness_constraint()

    def get_from_model(self, model: smt.SMTModel) -> AtomicFormula:
        """
        Get a concrete atomic formula from the model
        """
        node_value = self.node.get_from_model(model)

        if node_value == 0:
            return Falsum()
        elif node_value == 1:
            return Verum()
        else:
            symbol = self.language.relation_symbols[node_value - 2]
            arity = len(symbol.input_sorts)
            return RelationApplication(symbol, tuple(subterm.get_from_model(model) for subterm in self.subterms[:arity]))

    def equals(self, value: AtomicFormula) -> smt.SMTTerm:
        """
        Return a constraint saying that the variable equals the given atomic formula
        """
        if isinstance(value, Falsum):
            return self.node.equals(0)
        elif isinstance(value, Verum):
            return self.node.equals(1)
        elif isinstance(value, RelationApplication):
            symbol_index = self.language.relation_symbols.index(value.relation_symbol)
            arity = len(value.relation_symbol.input_sorts)

            return smt.And(
                self.node.equals(symbol_index + 2),
                *(subterm.equals(argument) for argument, subterm in zip(value.arguments, self.subterms[:arity])),
            )

        assert False, f"unexpected atomic formula {value}"

    def get_well_formedness_constraint(self) -> smt.SMTTerm:
        constraint = smt.FALSE()

        for node_value in range(0, 2 + len(self.language.relation_symbols)):
            if node_value == 0 or node_value == 1:
                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        *(subterm.get_is_null_constraint() for subterm in self.subterms),
                    ),
                    constraint,
                )
            else:
                symbol = self.language.relation_symbols[node_value - 2]
                arity = len(symbol.input_sorts)

                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        *(subterm.get_well_formedness_constraint(sort) for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])),
                        *(subterm.get_is_null_constraint() for subterm in self.subterms[arity:]),
                    ),
                    constraint,
                )

        return constraint
