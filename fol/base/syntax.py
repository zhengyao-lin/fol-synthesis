"""
Syntax of many-sorted first-order logic
"""

from __future__ import annotations

from typing import TypeVar, Generic, Tuple, Union, Mapping, Set
from dataclasses import dataclass
from abc import ABC, abstractmethod

from fol.smt import smt
from fol.synthesis.template import Template

from .language import BaseAST, Sort, FunctionSymbol, RelationSymbol, Language
from .semantics import Structure


_T = TypeVar("_T")


class Interpretable(Generic[_T], ABC):
    @abstractmethod
    def substitute(self, substitution: Mapping[Variable, Term]) -> _T: ...

    @abstractmethod
    def get_free_variables(self) -> Set[Variable]: ...

    @abstractmethod
    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm: ...


class Term(BaseAST, Template["Term"], Interpretable["Term"], ABC):
    def equals(self, value: Term) -> smt.SMTTerm:
        raise NotImplementedError()

    def get_sort(self) -> Sort:
        raise NotImplementedError()


class Formula(BaseAST, Template["Formula"], Interpretable["Formula"], ABC):
    def equals(self, value: Formula) -> smt.SMTTerm:
        raise NotImplementedError()

    def quantify_all_free_variables(self) -> Formula:
        free_vars = tuple(self.get_free_variables())
        formula = self

        for var in free_vars:
            formula = UniversalQuantification(var, formula)

        return formula

    def strip_universal_quantifiers(self) -> Formula:
        return self

    def __hash__(self) -> int:
        raise NotImplementedError()


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        assert self in valuation, \
               f"unable to interpret {self}"
        return valuation[self]
    
    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Term:
        return self

    def equals(self, value: Term) -> smt.SMTTerm:
        return smt.Bool(self == value)

    def get_sort(self) -> Sort:
        return self.sort


@dataclass(frozen=True)
class Application(Term):
    function_symbol: FunctionSymbol
    arguments: Tuple[Term, ...]

    def __str__(self) -> str:
        argument_string = ", ".join((str(arg) for arg in self.arguments))
        return f"{self.function_symbol.name}({argument_string})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Term:
        return Application(self.function_symbol, tuple(argument.substitute(substitution) for argument in self.arguments))

    def get_free_variables(self) -> Set[Variable]:
        free_vars = set()
        for argument in self.arguments:
            free_vars.update(argument.get_free_variables())
        return free_vars

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return structure.interpret_function(
            self.function_symbol,
            *(argument.interpret(structure, valuation) for argument in self.arguments),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(*(argument.get_constraint() for argument in self.arguments))

    def get_from_smt_model(self, model: smt.SMTModel) -> Term:
        return self

    def equals(self, value: Term) -> smt.SMTTerm:
        if not isinstance(value, Application) or value.function_symbol != self.function_symbol:
            return smt.FALSE()
        return smt.And(*(argument.equals(other_argument) for argument, other_argument in zip(self.arguments, value.arguments)))

    def get_sort(self) -> Sort:
        assert len(self.arguments) == len(self.function_symbol.input_sorts), \
               f"ill-formed term {self}"
        for argument, sort in zip(self.arguments, self.function_symbol.input_sorts):
            assert argument.get_sort() == sort, \
                   f"ill-sorted term {self}"

        return self.function_symbol.output_sort


@dataclass(frozen=True)
class Verum(Formula):
    def __str__(self) -> str:
        return "⊤"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return self

    def get_free_variables(self) -> Set[Variable]:
        return set()

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.TRUE()

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return self

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.Bool(self == value)


@dataclass(frozen=True)
class Falsum(Formula):
    def __str__(self) -> str:
        return "⊥"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return self

    def get_free_variables(self) -> Set[Variable]:
        return set()

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.FALSE()

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return self

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.Bool(self == value)


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return structure.interpret_relation(
            self.relation_symbol,
            *(argument.interpret(structure, valuation) for argument in self.arguments),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(*(argument.get_constraint() for argument in self.arguments))

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return RelationApplication(
            self.relation_symbol,
            tuple(argument.get_from_smt_model(model) for argument in self.arguments),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, RelationApplication) or value.relation_symbol != self.relation_symbol:
            return smt.FALSE()
        return smt.And(*(argument.equals(other_argument) for argument, other_argument in zip(self.arguments, value.arguments)))


AtomicFormula = Union[Verum, Falsum, RelationApplication]


@dataclass(frozen=True)
class Conjunction(Formula):
    left: Formula
    right: Formula

    @staticmethod
    def from_conjuncts(*conjuncts: Formula) -> Formula:
        if len(conjuncts) == 0:
            return Verum()

        formula = conjuncts[-1]

        for conjunct in conjuncts[:-1][::-1]:
            formula = Conjunction(conjunct, formula)

        return formula

    def __str__(self) -> str:
        return f"({self.left} /\\ {self.right})"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Conjunction(
            self.left.substitute(substitution),
            self.right.substitute(substitution),
        )

    def get_free_variables(self) -> Set[Variable]:
        return self.left.get_free_variables().union(self.right.get_free_variables())

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.And(
            self.left.interpret(structure, valuation),
            self.right.interpret(structure, valuation),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.left.get_constraint(), self.right.get_constraint())

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Conjunction(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Conjunction):
            return smt.FALSE()
        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.Or(
            self.left.interpret(structure, valuation),
            self.right.interpret(structure, valuation),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.left.get_constraint(), self.right.get_constraint())

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Disjunction(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Disjunction):
            return smt.FALSE()
        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )


@dataclass(frozen=True)
class Negation(Formula):
    formula: Formula

    def __str__(self) -> str:
        return f"not {self.formula}"

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        return Negation(self.formula.substitute(substitution))

    def get_free_variables(self) -> Set[Variable]:
        return self.formula.get_free_variables()

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.Not(self.formula.interpret(structure, valuation))

    def get_constraint(self) -> smt.SMTTerm:
        return self.formula.get_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Negation(self.formula.get_from_smt_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Negation):
            return smt.FALSE()
        return self.formula.equals(value.formula)


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.Implies(
            self.left.interpret(structure, valuation),
            self.right.interpret(structure, valuation),
        )

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.left.get_constraint(), self.right.get_constraint())

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Implication(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Implication):
            return smt.FALSE()
        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.Iff(
            self.left.interpret(structure, valuation),
            self.right.interpret(structure, valuation),
        )
    
    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.left.get_constraint(), self.right.get_constraint())

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return Equivalence(
            self.left.get_from_smt_model(model),
            self.right.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, Equivalence):
            return smt.FALSE()
        return smt.And(
            self.left.equals(value.left),
            self.right.equals(value.right),
        )


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        carrier = structure.interpret_sort(self.variable.sort)
        smt_var = smt.FreshSymbol(carrier.get_smt_sort())
        interp = self.body.interpret(structure, { **valuation, self.variable: smt_var })
        return carrier.universally_quantify(smt_var, interp)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.variable.get_constraint(), self.body.get_constraint())

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return UniversalQuantification(
            self.variable,
            self.body.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, UniversalQuantification) or \
           value.variable != self.variable:
            return smt.FALSE()
        return self.body.equals(value.body)

    def strip_universal_quantifiers(self) -> Formula:
        return self.body.strip_universal_quantifiers()


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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        carrier = structure.interpret_sort(self.variable.sort)
        smt_var = smt.FreshSymbol(carrier.get_smt_sort())
        interp = self.body.interpret(structure, { **valuation, self.variable: smt_var })
        return carrier.existentially_quantify(smt_var, interp)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.variable.get_constraint(), self.body.get_constraint())

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        return ExistentialQuantification(
            self.variable,
            self.body.get_from_smt_model(model),
        )

    def equals(self, value: Formula) -> smt.SMTTerm:
        if not isinstance(value, ExistentialQuantification) or \
           value.variable != self.variable:
            return smt.FALSE()
        return self.body.equals(value.body)
