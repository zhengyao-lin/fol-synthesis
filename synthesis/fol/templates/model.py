from typing import Mapping, Dict, Optional
from collections import OrderedDict

from synthesis.smt import smt
from synthesis.template import Template

from ..base import *


class ModelTemplate(Template[Structure], Structure):
    """
    A model variable can act as a structure, i.e. a formula can be
    interpreted in it, but at the same time it can be used as
    a template to synthesize an actual concrete model
    """


class UninterpretedModelTemplate(SymbolicStructure, ModelTemplate):
    """
    A structure in which all uninterpreted sorts are assigned
    the carrier <default_sort> and all uninterpreted functions/relations
    are assigned uninterpreted SMT functions
    """

    def __init__(self, language: Language, default_sort: Optional[smt.SMTSort] = None):
        """
        If default_sort is None, fresh uninterpreted SMT sorts will be used for each uninterpreted sort in the language
        """

        carriers: Dict[Sort, CarrierSet] = OrderedDict()
        function_interpretations: Dict[FunctionSymbol, smt.SMTFunction] = OrderedDict()
        relation_interpretations: Dict[RelationSymbol, smt.SMTFunction] = OrderedDict()

        for sort in language.sorts:
            if sort.smt_hook is None:
                # TODO
                carriers[sort] = RefinementCarrierSet(default_sort or smt.FreshSort())
            else:
                carriers[sort] = RefinementCarrierSet(sort.smt_hook)

        for function_symbol in language.function_symbols:
            if function_symbol.smt_hook is None:
                smt_input_sorts = tuple(carriers[sort].get_smt_sort() for sort in function_symbol.input_sorts)
                smt_output_sort = carriers[function_symbol.output_sort].get_smt_sort()
                function_interpretations[function_symbol] = smt.FreshFunction(smt_input_sorts, smt_output_sort)

        for relation_symbol in language.relation_symbols:
            if relation_symbol.smt_hook is None:
                smt_input_sorts = tuple(carriers[sort].get_smt_sort() for sort in relation_symbol.input_sorts)
                relation_interpretations[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.BOOL)

        super().__init__(language, carriers, function_interpretations, relation_interpretations)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Structure:
        """
        Concretize all functions
        """
        concrete_functions = OrderedDict()
        concrete_relations = OrderedDict()

        # construct new function interpretations
        for function_symbol in self.language.function_symbols:
            if function_symbol.smt_hook is None:
                concrete_functions[function_symbol] = \
                    (lambda symbol: lambda *args: \
                        model.get_value(self.interpret_function(symbol, *args), model_completion=False))(function_symbol)

        # construct new relation interpretations
        for relation_symbol in self.language.relation_symbols:
            if relation_symbol.smt_hook is None:
                concrete_relations[relation_symbol] = \
                    (lambda symbol: lambda *args: \
                        model.get_value(self.interpret_relation(symbol, *args), model_completion=False))(relation_symbol)

        return SymbolicStructure(self.language, self.carriers, concrete_functions, concrete_relations)

    def equals(self, value: Structure) -> smt.SMTTerm:
        raise NotImplementedError()


class FiniteFOModelTemplate(UninterpretedModelTemplate):
    """
    A variable/template for a FO model of a given theory
    in which all interpreted sorts have finite domains
    """

    def __init__(self, theory: Theory, size_bounds: Mapping[Sort, int]):
        super().__init__(theory.language, smt.INT)

        self.theory = theory

        # set all carrier sets to finite sets
        for sort in theory.language.sorts:
            if sort.smt_hook is None:
                assert sort in size_bounds, \
                       f"no bound on the size of the carrier set of {sort}"
                carrier = FiniteCarrierSet(
                    smt.INT,
                    tuple(smt.FreshSymbol(smt.INT) for _ in range(size_bounds[sort]))
                )
                self.carriers[sort] = carrier

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
                constraint = smt.And(sentence.formula.interpret(self, {}), constraint)
            elif isinstance(sentence, FixpointDefinition):
                constraint = smt.And(sentence.as_formula().interpret(self, {}), constraint)
            else:
                assert False, f"unsupported sentence {sentence}"

        return constraint

    def get_from_smt_model(self, model: smt.SMTModel) -> Structure:
        """
        Get a concrete finite structure
        """

        uninterp_structure = super().get_from_smt_model(model)

        concrete_carriers = OrderedDict()
        concrete_functions = OrderedDict()
        concrete_relations = OrderedDict()

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
                        uninterp_structure.interpret_function(symbol, *args))(function_symbol)

        # construct new relation interpretations
        for relation_symbol in self.theory.language.relation_symbols:
            if relation_symbol.smt_hook is None:
                concrete_relations[relation_symbol] = \
                    (lambda symbol: lambda *args: \
                        uninterp_structure.interpret_relation(symbol, *args))(relation_symbol)

        return SymbolicStructure(self.theory.language, concrete_carriers, concrete_functions, concrete_relations)


class FiniteLFPModelTemplate(FiniteFOModelTemplate):
    """
    Similar to FiniteFOModelTemplate except having extra
    constraint to enforce the fixpoint definitions to be
    least fixpoints.
    """

    def __init__(self, theory: Theory, size_bounds: Mapping[Sort, int]):
        super().__init__(theory, size_bounds)

        self.rank_functions: Dict[RelationSymbol, smt.SMTFunction] = OrderedDict()

        # for any fixpoint definition, add a rank function
        for sentence in theory.sentences:
            if isinstance(sentence, FixpointDefinition):
                relation_symbol = sentence.relation_symbol
                assert relation_symbol not in self.rank_functions, \
                       f"duplicate fixpoint definition for {relation_symbol}"
                smt_input_sorts = tuple(self.interpret_sort(sort).get_smt_sort() for sort in relation_symbol.input_sorts)
                self.rank_functions[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.INT)

    def get_constraint(self) -> smt.SMTTerm:
        """
        The model should satify all sentences in the theory
        """
        constraint = super().get_constraint()
        
        for sentence in self.theory.sentences:
            if isinstance(sentence, FixpointDefinition):
                constraint = smt.And(self.get_constraints_for_least_fixpoint(sentence), constraint)

        return constraint

    def get_constraints_for_least_fixpoint(self, definition: FixpointDefinition) -> smt.SMTTerm:
        """
        Return a constraint saying that the structure satisfies the given fixpoint definition (as least fixpoint)
        """
        
        # enforcing fixpoint
        # NOTE: this is already added in FiniteFOModelTemplate
        # constraint = definition.as_formula().interpret(self, {})

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

        # state the rank invariant
        # TODO: slightly hacky
        valuation = OrderedDict({ k: v for k, v in zip(definition.variables, smt_input_vars) })

        # interpret the definition but with the relation R(...) replaced by
        # f(...) < f(x)  /\ R(...)
        old_interpretation = self.relation_interpretations[relation_symbol]
        self.relation_interpretations[relation_symbol] = lambda *args: \
            smt.And(
                smt.LT(rank_function(*args), rank_function(*smt_input_vars)),
                old_interpretation(*args),
            )
        interp = definition.definition.interpret(self, valuation)
        self.relation_interpretations[relation_symbol] = old_interpretation

        rank_invariant = smt.Implies(
            old_interpretation(*smt_input_vars),
            interp
        )

        # forall. R(...) -> phi((f(...) < f(x)  /\ R(...)) / R(...))
        for var, sort in zip(smt_input_vars, relation_symbol.input_sorts):
            carrier = self.interpret_sort(sort)
            rank_invariant = carrier.universally_quantify(var, rank_invariant)

        return smt.And(non_negative_constraint, rank_invariant)


class FOProvableModelTemplate(UninterpretedModelTemplate):
    """
    A structure such that in a theory with fixpoint definitions,
    if a formula phi is FO-provable with <unfold_depth> unfoldings of the
    fixpoint definitions, then the structure satisfies phi.
    """

    def __init__(self, theory: Theory, unfold_depth: int):
        super().__init__(theory.language)

        self.theory = theory

        # unfold LFP definitions
        overrides = OrderedDict()
        for sentence in theory.sentences:
            if isinstance(sentence, FixpointDefinition):
                unfolded_definition = sentence.unfold_definition(unfold_depth)
                overrides[sentence.relation_symbol] = \
                    self.interpret_fixpoint_definition(unfolded_definition)

        self.relation_interpretations.update(overrides)

    def get_constraint(self) -> smt.SMTTerm:
        # NOTE: fixpoint axioms are not included here

        constraint = smt.TRUE()
        for sentence in self.theory.sentences:
            if isinstance(sentence, Axiom):
                constraint = smt.And(sentence.formula.interpret(self, {}), constraint)
        
        return constraint

    def interpret_fixpoint_definition(self, definition: FixpointDefinition) -> smt.SMTFunction:
        """
        Interpret the fixpoint definition in the current structure as an SMT function
        """
        valuation = OrderedDict({
            var: smt.FreshSymbol(self.get_smt_sort(var.sort))
            for var in definition.variables
        })
        smt_formula = definition.definition.interpret(self, valuation)

        def interp(*args: smt.SMTTerm) -> smt.SMTTerm:
            assert len(args) == len(definition.variables)
            substitution = OrderedDict({ valuation[k]: v for k, v in zip(definition.variables, args) })
            return smt_formula.substitute(substitution) # substitution on the SMT formula

        return interp
