from typing import Any, Generic, TypeVar, Tuple, Mapping, Dict, Generator

from dataclasses import dataclass
from abc import ABC, abstractmethod

import itertools

from .fol.ast import *
from .structure import CarrierSet, Structure, FiniteCarrierSet, SymbolicStructure, RefinementCarrierSet
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

    def get_free_variables(self) -> Tuple[Variable, ...]:
        return self.free_vars

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
            else:
                symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
                arity = len(symbol.input_sorts)

                if symbol.output_sort == sort and (self.depth != 0 or arity == 0):
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

    def interpret_in_structure(self, sort: Sort, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        """
        Interpret the undetermined term in the given structure and valuation
        """

        carrier = structure.interpret_sort(sort)
        interp = smt.FreshSymbol(carrier.get_smt_sort())

        for node_value in range(1, len(self.free_vars) + len(self.language.function_symbols) + 1):
            if node_value <= len(self.free_vars):
                variable = self.free_vars[node_value - 1]
                if variable.sort == sort:
                    assert variable in valuation, f"unable to interpret variable {variable}"
                    interp = smt.Ite(self.node.equals(node_value), valuation[variable], interp)

            else:
                symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
                arity = len(symbol.input_sorts)

                if symbol.output_sort == sort and (self.depth != 0 or arity == 0):
                    arguments = tuple(
                        subterm.interpret_in_structure(subterm_sort, structure, valuation)
                        for subterm_sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])
                    )
                    interp = smt.Ite(self.node.equals(node_value), structure.interpret_function(symbol, *arguments), interp)

        return interp


class FormulaVariable(VariableWithConstraint[Formula]):
    @abstractmethod
    def get_free_variables(self) -> Tuple[Variable, ...]: ...

    @abstractmethod
    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm: ...


class ConstantFormula(FormulaVariable):
    def __init__(self, formula: Formula):
        self.formula = formula

    def get_free_variables(self) -> Tuple[Variable, ...]:
        return tuple(self.formula.get_free_variables())

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_model(self, model: smt.SMTModel) -> Formula:
        return self.formula

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.TRUE() if value == self.formula else smt.FALSE()

    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        return structure.interpret_formula(self.formula, valuation)


class AtomicFormulaVariable(FormulaVariable):
    """
    Template for an atomic formula (i.e. false, true, or other relations)
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], term_depth: int):
        self.language = language
        self.free_vars = free_vars
        self.term_depth = term_depth
        self.node = BoundedIntegerVariable(0, 2 + len(language.relation_symbols))

        self.subterms = tuple(TermVariable(language, free_vars, term_depth) for _ in range(language.get_max_relation_arity()))

    def get_free_variables(self) -> Tuple[Variable, ...]:
        return self.free_vars

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

    def equals(self, value: Formula) -> smt.SMTTerm:
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

    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        """
        Interpret the undetermined atomic formula in the given structure and valuation
        """

        interp = smt.FALSE()

        for node_value in range(0, 2 + len(self.language.relation_symbols)):
            if node_value == 0:
                interp = smt.Ite(self.node.equals(node_value), smt.FALSE(), interp)

            elif node_value == 1:
                interp = smt.Ite(self.node.equals(node_value), smt.TRUE(), interp)

            else:
                symbol = self.language.relation_symbols[node_value - 2]
                arity = len(symbol.input_sorts)
                arguments = tuple(
                    subterm.interpret_in_structure(sort, structure, valuation)
                    for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])
                )
                interp = smt.Ite(self.node.equals(node_value), structure.interpret_relation(symbol, *arguments), interp)

        return interp


@dataclass
class ConjunctionFormulaVariable(FormulaVariable):
    conjuncts: Tuple[FormulaVariable, ...]

    def __post_init__(self) -> None:
        assert len(self.conjuncts) != 0

    def get_free_variables(self) -> Tuple[Variable, ...]:
        return tuple(set(sum(map(lambda c: c.get_free_variables(), self.conjuncts), ())))

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(*(conjunct.get_constraint() for conjunct in self.conjuncts))

    def get_from_model(self, model: smt.SMTModel) -> Formula:
        conjuncts = tuple(conjunct.get_from_model(model) for conjunct in self.conjuncts)
        formula = conjuncts[-1]

        for conjunct in conjuncts[:-1][::-1]:
            formula = Conjunction(conjunct, formula)

        return formula

    def equals(self, value: Formula) -> smt.SMTTerm:
        constraint = smt.TRUE()

        for i, conjunct in enumerate(self.conjuncts):
            if i + 1 != len(self.conjuncts):
                assert isinstance(value, Conjunction)
                constraint = smt.And(conjunct.equals(value.left), constraint)
                value = value.right
            else:
                constraint = smt.And(conjunct.equals(value), constraint)

        return constraint

    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        return smt.And(*(
            conjunct.interpret_in_structure(structure, valuation)
            for conjunct in self.conjuncts
        ))


@dataclass
class DisjunctionFormulaVariable(FormulaVariable):
    disjuncts: Tuple[FormulaVariable, ...]

    def __post_init__(self) -> None:
        assert len(self.disjuncts) != 0

    def get_free_variables(self) -> Tuple[Variable, ...]:
        return tuple(set(sum(map(lambda c: c.get_free_variables(), self.disjuncts), ())))

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(*(disjunct.get_constraint() for disjunct in self.disjuncts))

    def get_from_model(self, model: smt.SMTModel) -> Formula:
        disjuncts = tuple(disjunct.get_from_model(model) for disjunct in self.disjuncts)
        formula = disjuncts[-1]

        for disjunct in disjuncts[:-1][::-1]:
            formula = Disjunction(disjunct, formula)

        return formula

    def equals(self, value: Formula) -> smt.SMTTerm:
        constraint = smt.TRUE()

        for i, disjunct in enumerate(self.disjuncts):
            if i + 1 != len(self.disjuncts):
                assert isinstance(value, Disjunction)
                constraint = smt.And(disjunct.equals(value.left), constraint)
                value = value.right
            else:
                constraint = smt.And(disjunct.equals(value), constraint)

        return constraint

    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        return smt.Or(*(
            disjunct.interpret_in_structure(structure, valuation)
            for disjunct in self.disjuncts
        ))


@dataclass
class ImplicationFormulaVariable(FormulaVariable):
    left: FormulaVariable
    right: FormulaVariable

    def get_free_variables(self) -> Tuple[Variable, ...]:
        # TODO: order?
        return tuple(set(self.left.get_free_variables() + self.right.get_free_variables()))

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(self.left.get_constraint(), self.right.get_constraint())

    def get_from_model(self, model: smt.SMTModel) -> Formula:
        return Implication(self.left.get_from_model(model), self.right.get_from_model(model))

    def equals(self, value: Formula) -> smt.SMTTerm:
        assert isinstance(value, Implication)
        return smt.And(self.left.equals(value.left), self.right.equals(value.right))

    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        return smt.Implies(
            self.left.interpret_in_structure(structure, valuation),
            self.right.interpret_in_structure(structure, valuation),
        )


class QuantifierBlockFormulaVariable(FormulaVariable):
    def __init__(self, is_forall: bool, variables: Tuple[Variable, ...], body: FormulaVariable):
        self.is_forall = is_forall # True for forall, False for exists
        self.variables = variables
        self.body = body

    def get_free_variables(self) -> Tuple[Variable, ...]:
        return tuple(var for var in self.body.get_free_variables() if var not in self.variables)

    def get_constraint(self) -> smt.SMTTerm:
        return self.body.get_constraint()

    def get_from_model(self, model: smt.SMTModel) -> Formula:
        """
        Get a concrete atomic formula from the model
        """
        formula = self.body.get_from_model(model)

        for var in self.variables[::-1]:
            formula = UniversalQuantification(var, formula) if self.is_forall else ExistentialQuantification(var, formula)

        return formula

    def equals(self, value: Formula) -> smt.SMTTerm:
        for var in self.variables:
            if self.is_forall:
                assert isinstance(value, UniversalQuantification) and value.variable == var, \
                       f"cannot match the first quantifiers with variables {self.variables}"
            else:
                assert isinstance(value, ExistentialQuantification) and value.variable == var, \
                       f"cannot match the first quantifiers with variables {self.variables}"
            value = value.body

        return self.body.equals(value)

    def interpret_in_structure(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm] = {}) -> smt.SMTTerm:
        fresh_vars = structure.get_fresh_valuation(self.variables)
        interp = self.body.interpret_in_structure(structure, { **valuation, **fresh_vars })

        for var in self.variables[::-1]:
            carrier = structure.interpret_sort(var.sort)
            if self.is_forall:
                interp = carrier.universally_quantify(fresh_vars[var], interp)
            else:
                interp = carrier.existentially_quantify(fresh_vars[var], interp)

        return interp


class ForAllBlockFormulaVariable(QuantifierBlockFormulaVariable):
    def __init__(self, variables: Tuple[Variable, ...], body: FormulaVariable):
        super().__init__(True, variables, body)


class ExistsBlockFormulaVariable(QuantifierBlockFormulaVariable):
    def __init__(self, variables: Tuple[Variable, ...], body: FormulaVariable):
        super().__init__(False, variables, body)


class ModelVariable(VariableWithConstraint[Structure], Structure): ...


class FiniteLFPModelVariable(SymbolicStructure, ModelVariable):
    """
    A variable/template for a finite LFP model of a given theory
    """

    def __init__(self, theory: Theory, size_bounds: Mapping[Sort, int]):
        self.theory = theory

        carriers: Dict[Sort, FiniteCarrierSet] = {}
        function_interpretations: Dict[FunctionSymbol, smt.SMTFunction] = {}
        relation_interpretations: Dict[RelationSymbol, smt.SMTFunction] = {}

        self.rank_functions: Dict[RelationSymbol, smt.SMTFunction] = {}

        # initialize all carrier sets
        for sort in theory.language.sorts:
            if sort.smt_hook is None:
                assert sort in size_bounds, \
                       f"no bound on the size of the carrier set of {sort}"
                carrier = FiniteCarrierSet(
                    smt.INT,
                    tuple(smt.FreshSymbol(smt.INT) for _ in range(size_bounds[sort]))
                )
                carriers[sort] = carrier

        # initialize uninterpreted functions for function symbols
        for function_symbol in theory.language.function_symbols:
            if function_symbol.smt_hook is None:
                smt_input_sorts = tuple(sort.smt_hook or smt.INT for sort in function_symbol.input_sorts)
                smt_output_sort = function_symbol.output_sort.smt_hook or smt.INT
                function_interpretations[function_symbol] = smt.FreshFunction(smt_input_sorts, smt_output_sort)

        # initialize uninterpreted functions for relation symbols
        for relation_symbol in theory.language.relation_symbols:
            if relation_symbol.smt_hook is None:
                smt_input_sorts = tuple(sort.smt_hook or smt.INT for sort in relation_symbol.input_sorts)
                relation_interpretations[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.BOOL)

        # for any fixpoint definition, add a rank function
        for sentence in theory.sentences:
            if isinstance(sentence, FixpointDefinition):
                relation_symbol = sentence.relation_symbol
                assert relation_symbol not in self.rank_functions, \
                       f"duplicate fixpoint definition for {relation_symbol}"
                smt_input_sorts = tuple(sort.smt_hook or smt.INT for sort in relation_symbol.input_sorts)
                self.rank_functions[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.INT)

        super().__init__(theory.language, carriers, function_interpretations, relation_interpretations)

    def get_constraint(self) -> smt.SMTTerm:
        """
        The model should satify all sentences in the theory
        """
        constraint = smt.TRUE()

        # all functions are closed
        for function_symbol in self.theory.language.function_symbols:
            if function_symbol.smt_hook is None and function_symbol.output_sort.smt_hook is None:
                output_carrier = self.interpret_sort(function_symbol.output_sort)
                assert isinstance(output_carrier, FiniteCarrierSet)

                smt_input_vars = tuple(smt.FreshSymbol(sort.smt_hook or smt.INT) for sort in function_symbol.input_sorts)

                closed_constraint = smt.Or(*(
                    smt.Equals(self.interpret_function(function_symbol, *smt_input_vars), element)
                    for element in output_carrier.domain
                ))

                for var, sort in zip(smt_input_vars, function_symbol.input_sorts):
                    carrier = self.interpret_sort(sort)
                    closed_constraint = carrier.universally_quantify(var, closed_constraint)

                constraint = smt.And(closed_constraint, constraint)
        
        for sentence in self.theory.sentences:
            if isinstance(sentence, Axiom):
                constraint = smt.And(self.interpret_formula(sentence.formula), constraint)
            elif isinstance(sentence, FixpointDefinition):
                constraint = smt.And(self.get_constraints_for_least_fixpoint(sentence), constraint)
            else:
                assert False, f"unsupported sentence {sentence}"

        return constraint

    def get_constraints_for_least_fixpoint(self, definition: FixpointDefinition) -> smt.SMTTerm:
        """
        Return a constraint saying that the structure satisfies the given fixpoint definition (as least fixpoint)
        """
        
        # enforcing fixpoint
        constraint = self.interpret_formula(definition.as_formula())

        # use a rank function to enforce the least fixpoint
        relation_symbol = definition.relation_symbol
        rank_function = self.rank_functions[relation_symbol]

        # state that the rank is non-negative
        smt_input_sorts = tuple(self.get_smt_sort(sort) for sort in relation_symbol.input_sorts)
        smt_input_vars = tuple(smt.FreshSymbol(smt_sort) for smt_sort in smt_input_sorts)
        non_negative_constraint = smt.GE(rank_function(*smt_input_vars), smt.Int(0))

        for var, sort in zip(smt_input_vars, relation_symbol.input_sorts):
            carrier = self.interpret_sort(sort)
            non_negative_constraint = carrier.universally_quantify(var, non_negative_constraint)

        constraint = smt.And(non_negative_constraint, constraint)

        # state the rank invariant
        # TODO: slightly hacky
        valuation = { k: v for k, v in zip(definition.variables, smt_input_vars) }

        # interpret the definition but with the relation R(...) replaced by
        # f(...) < f(x)  /\ R(...)
        old_interpretation = self.relation_interpretations[relation_symbol]
        self.relation_interpretations[relation_symbol] = lambda *args: \
            smt.And(
                smt.LT(rank_function(*args), rank_function(*smt_input_vars)),
                old_interpretation(*args),
            )
        interp = self.interpret_formula(definition.definition, valuation)
        self.relation_interpretations[relation_symbol] = old_interpretation

        rank_invariant = smt.Implies(
            old_interpretation(*smt_input_vars),
            interp
        )

        # forall. R(...) -> phi((f(...) < f(x)  /\ R(...)) / R(...))
        for var, sort in zip(smt_input_vars, relation_symbol.input_sorts):
            carrier = self.interpret_sort(sort)
            rank_invariant = carrier.universally_quantify(var, rank_invariant)

        constraint = smt.And(rank_invariant, constraint)

        return constraint

    def get_from_model(self, model: smt.SMTModel) -> Structure:
        """
        Concretize a structure
        """
        concrete_carriers = {}
        concrete_functions = {}
        concrete_relations = {}

        for sort in self.theory.language.sorts:
            if sort.smt_hook is None:
                carrier = self.interpret_sort(sort)
                assert isinstance(carrier, FiniteCarrierSet)

                # read the concrete domain
                concrete_carriers[sort] = FiniteCarrierSet(
                    carrier.get_smt_sort(),
                    tuple(model[element] for element in carrier.domain),
                )

        # construct new function interpretations
        for function_symbol in self.theory.language.function_symbols:
            if function_symbol.smt_hook is None:
                concrete_functions[function_symbol] = \
                    (lambda symbol: lambda *args: \
                        model.get_value(self.interpret_function(symbol, *args), model_completion=False))(function_symbol)

        # construct new relation interpretations
        for relation_symbol in self.theory.language.relation_symbols:
            if relation_symbol.smt_hook is None:
                concrete_relations[relation_symbol] = \
                    (lambda symbol: lambda *args: \
                        model.get_value(self.interpret_relation(symbol, *args), model_completion=False))(relation_symbol)

        return SymbolicStructure(self.theory.language, concrete_carriers, concrete_functions, concrete_relations)

    def equals(self, value: Structure) -> smt.SMTTerm:
        raise NotImplementedError()


class UninterpretedStructure(SymbolicStructure):
    """
    A structure in which all uninterpreted sorts are assigned
    the carrier INT and all uninterpreted functions/relations
    are assigned uninterpreted SMT functions
    """

    def __init__(self, language: Language):
        carriers: Dict[Sort, CarrierSet] = {}
        function_interpretations: Dict[FunctionSymbol, smt.SMTFunction] = {}
        relation_interpretations: Dict[RelationSymbol, smt.SMTFunction] = {}

        for sort in language.sorts:
            if sort.smt_hook is None:
                carriers[sort] = RefinementCarrierSet(smt.INT)

        for function_symbol in language.function_symbols:
            if function_symbol.smt_hook is None:
                smt_input_sorts = tuple(sort.smt_hook or smt.INT for sort in function_symbol.input_sorts)
                smt_output_sort = function_symbol.output_sort.smt_hook or smt.INT
                function_interpretations[function_symbol] = smt.FreshFunction(smt_input_sorts, smt_output_sort)

        for relation_symbol in language.relation_symbols:
            if relation_symbol.smt_hook is None:
                smt_input_sorts = tuple(sort.smt_hook or smt.INT for sort in relation_symbol.input_sorts)
                relation_interpretations[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.BOOL)

        super().__init__(language, carriers, function_interpretations, relation_interpretations)


class FOProvableStructure(UninterpretedStructure):
    """
    A structure such that in a theory with fixpoint definitions,
    if a formula phi is FO-provable with <unfold_depth> unfoldings of the
    fixpoint definitions, then the structure satisfies phi.
    """

    def __init__(self, theory: Theory, unfold_depth: int):
        super().__init__(theory.language)

        overrides = {}

        # unfold LFP definitions
        for sentence in theory.sentences:
            if isinstance(sentence, FixpointDefinition):
                unfolded_definition = sentence.unfold_definition(unfold_depth)
                overrides[sentence.relation_symbol] = \
                    self.interpret_fixpoint_definition(unfolded_definition)

        self.relation_interpretations.update(overrides)

    def interpret_fixpoint_definition(self, definition: FixpointDefinition) -> smt.SMTFunction:
        """
        Interpret the fixpoint definition in the current structure as an SMT function
        """
        valuation = self.get_fresh_valuation(definition.variables)
        smt_formula = self.interpret_formula(definition.definition, valuation)

        def interp(*args: smt.SMTTerm) -> smt.SMTTerm:
            assert len(args) == len(definition.variables)
            substitution = { valuation[k]: v for k, v in zip(definition.variables, args) }
            return smt_formula.substitute(substitution) # substitution on the SMT formula

        return interp


class CEIGSynthesizer:
    """
    Synthesize formulas that are (approximately) LFP-valid in a given theory
    but not FO-provable under some unfolding depth
    """

    def __init__(
        self,
        theory: Theory,
        formula_var: FormulaVariable,
        counterexample_var: ModelVariable,
        fo_provable_depth: int,
    ):
        """
        <theory> is the theory in which the synthesized formulas should hold
        <formula_var> is the template for the formula to be synthesized
        <model_var> is the template for a counterexample model
        <fo_provable_depth> indicates that the synthesized formula should not be FO-provable at that unfolding depth
        """

        self.theory = theory
        self.formula_var = formula_var
        self.counterexample_var = counterexample_var
        self.fo_provable_structure = FOProvableStructure(theory, fo_provable_depth)

    def synthesize(self, solver_name: str = "z3") -> Generator[Formula, None, None]:
        free_vars = self.formula_var.get_free_variables()

        with smt.Solver(name=solver_name) as gen_solver, smt.Solver(name=solver_name) as check_solver:
            # gen_solver is used to generate candidates
            # check_solver is used to generate counterexamples

            # load templates to solvers
            self.formula_var.add_to_solver(gen_solver)
            self.counterexample_var.add_to_solver(check_solver)

            # when negated, the (universally quantified) free variables
            # become existentially quantified, we do skolemization here
            gen_skolem_constants = { # for the fo provable structure
                v: self.fo_provable_structure.interpret_sort(v.sort).get_fresh_constant(gen_solver, v.sort)
                for v in free_vars
            }
            check_skolem_constants = { # for the counterexample
                v: self.counterexample_var.interpret_sort(v.sort).get_fresh_constant(check_solver, v.sort)
                for v in free_vars
            }

            # the formula should not be FO provable
            gen_solver.add_assertion(smt.Not(self.formula_var.interpret_in_structure(self.fo_provable_structure, gen_skolem_constants)))

            while gen_solver.solve():
                # get a candidate from the SMT model
                candidate = self.formula_var.get_from_model(gen_solver.get_model())
                print(candidate, "... ", end="", flush=True)

                # try to find a finite counterexample
                check_solver.push()
                check_solver.add_assertion(smt.Not(self.counterexample_var.interpret_formula(candidate, check_skolem_constants)))

                if check_solver.solve():
                    # a concrete counterexample
                    counterexample = self.counterexample_var.get_from_model(check_solver.get_model())
                    check_solver.pop()

                    # add the new counterexample
                    print("✘")
                    gen_solver.add_assertion(
                        ForAllBlockFormulaVariable(
                            free_vars,
                            self.formula_var,
                        ).interpret_in_structure(counterexample),
                    )
                else:
                    check_solver.pop()
                    # no counterexample found, maybe this is true
                    print("✓")

                    # add duplication-avoidance constraint
                    for assignment in itertools.permutations(gen_skolem_constants.values()):
                        permuted_skolem_constants = dict(zip(free_vars, assignment))
                        gen_solver.add_assertion(self.fo_provable_structure.interpret_formula(candidate, permuted_skolem_constants))

                    # output the candidate
                    yield candidate
