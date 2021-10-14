from typing import Mapping, Dict, Optional, List
from collections import OrderedDict

import itertools

from synthesis.smt import smt
from synthesis.template import Template

from ..base import *


class StructureTemplate(Template[Structure], Structure):
    """
    A model variable can act as a structure, i.e. a formula can be
    interpreted in it, but at the same time it can be used as
    a template to synthesize an actual concrete model
    """


class UninterpretedStructureTemplate(SymbolicStructure, StructureTemplate):
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


class FOModelTemplate(UninterpretedStructureTemplate):
    def __init__(self, theory: Theory, default_sort: Optional[smt.SMTSort] = None):
        super().__init__(theory.language, default_sort)
        self.theory = theory

    def get_constraint(self) -> smt.SMTTerm:
        """
        The model should satify all sentences in the theory
        """
        constraint = smt.TRUE()

        for formula in self.theory.convert_to_fo_theory():
            constraint = smt.And(formula.interpret(self, {}), constraint)

        return constraint


class FiniteFOModelTemplate(UninterpretedStructureTemplate):
    """
    A variable/template for a FO model of a given theory
    in which all interpreted sorts have finite domains
    """

    def __init__(self, theory: Theory, size_bounds: Mapping[Sort, int], exact_size: bool = False):
        super().__init__(theory.language, smt.INT)

        self.theory = theory

        # set all carrier sets to finite sets
        for sort in theory.language.sorts:
            if sort.smt_hook is None:
                assert sort in size_bounds, \
                       f"no bound on the size of the carrier set of {sort}"
                carrier = FiniteCarrierSet(
                    smt.INT,
                    tuple(smt.Int(i) for i in range(size_bounds[sort])) if exact_size else
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

        for formula in self.theory.convert_to_fo_theory():
            constraint = smt.And(formula.interpret(self, {}), constraint)

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


class FiniteLFPModelTemplate(FiniteFOModelTemplate):
    """
    Similar to FiniteFOModelTemplate except having extra
    constraint to enforce the fixpoint definitions to be
    least fixpoints.
    """

    def __init__(
        self,
        theory: Theory,
        size_bounds: Mapping[Sort, int],
        fixpoint_bounds: Mapping[RelationSymbol, int] = {},
        # each relation R defined by fixpoint lies in R_1 x ... x R_n
        # Suppose R_1 x ... x R_m, m < n, is finite,
        # Then we put a bound on the size of each slice R(x_1, ..., x_m)
        # for any x_1, ..., x_m in R_1 x ... x R_m
    ):
        super().__init__(theory, size_bounds)

        # domains of finite fixpoint relations
        # A fixpoint relation is finite if
        #   - all of the input sorts are interpreted as finite sets in this structure
        #   - or, the relation has an explicit bound in <fixpoint_bounds>
        self.finite_fixpoint_domains: Dict[RelationSymbol, Tuple[Tuple[smt.SMTTerm, ...], ...]] = {}

        self.rank_functions: Dict[RelationSymbol, smt.SMTFunction] = OrderedDict()

        # for any fixpoint definition, add a rank function
        for definition in theory.get_fixpoint_definitions():
            relation_symbol = definition.relation_symbol
            assert relation_symbol not in self.rank_functions, \
                   f"duplicate fixpoint definition for {relation_symbol}"
            smt_input_sorts = tuple(self.interpret_sort(sort).get_smt_sort() for sort in relation_symbol.input_sorts)
            self.rank_functions[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.INT)

            finite_domain = self.get_finite_domain(relation_symbol, fixpoint_bounds.get(relation_symbol, definition.bound))

            if finite_domain is not None:
                self.finite_fixpoint_domains[relation_symbol] = finite_domain
                self.override_finite_fixpoint(relation_symbol, finite_domain)

    def get_finite_domain(
        self,
        relation_symbol: RelationSymbol,
        fixpoint_bound: Optional[int], 
    ) -> Optional[Tuple[Tuple[smt.SMTTerm, ...], ...]]:
        """
        Check if the domain of a relation can be made finite,
        if so, return SMT representations of the domain elements,
        otherwise, return None
        """

        domains: List[Tuple[Optional[smt.SMTTerm], ...]] = []
        non_finite_sorts: List[smt.SMTSort] = []
        is_finite = True

        # if all sorts are interpreted finitely, then the relation is finite
        for input_sort in relation_symbol.input_sorts:
            if input_sort.smt_hook is not None:
                is_finite = False
                non_finite_sorts.append(self.get_smt_sort(input_sort))
                domains.append((None,))
            else:
                carrier = self.interpret_sort(input_sort)
                assert isinstance(carrier, FiniteCarrierSet)
                domains.append(carrier.domain)
        
        if is_finite:
            return tuple(itertools.product(*domains))

        elif fixpoint_bound is not None:
            finite_domain: List[Tuple[smt.SMTTerm, ...]] = []

            # otherwise, the relation is finite if we specify a bound
            for finite_slice in itertools.product(*domains):
                for _ in range(fixpoint_bound):
                    non_finite_instance = tuple(smt.FreshSymbol(smt_sort) for smt_sort in non_finite_sorts)
                    non_finite_index = 0
                    instance: List[smt.SMTTerm] = []

                    for term in finite_slice:
                        if term is None:
                            assert non_finite_index < len(non_finite_instance)
                            instance.append(non_finite_instance[non_finite_index])
                            non_finite_index += 1
                        else:
                            instance.append(term)

                    finite_domain.append(tuple(instance))

            return tuple(finite_domain)

        return None

    def override_finite_fixpoint(self, relation_symbol: RelationSymbol, domain: Tuple[Tuple[smt.SMTTerm, ...], ...]) -> None:
        """
        Create a more compact representation of the relation using the given domain
        """
        switches: List[
            Tuple[
                Tuple[Tuple[smt.SMTTerm, ...], ...],
                smt.SMTTerm,
            ]
        ] = [ (elem, smt.FreshSymbol(smt.BOOL)) for elem in domain ]

        def relation(*args: smt.SMTTerm) -> smt.SMTTerm:
            return smt.Or(
                smt.And(
                    smt.And(smt.Equals(a, b) for a, b in zip(args, elem)),
                    switch,
                )
                for elem, switch in switches
            )

        self.relation_interpretations[relation_symbol] = relation

    def get_constraint(self) -> smt.SMTTerm:
        """
        The model should satify all sentences in the theory
        """
        constraint = super().get_constraint()

        for definition in self.theory.get_fixpoint_definitions():
            constraint = smt.And(self.get_constraints_for_least_fixpoint(definition), constraint)

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
        if relation_symbol in self.finite_fixpoint_domains:
            rank_invariant = smt.And(
                rank_invariant.substitute(dict(zip(smt_input_vars, elem)))
                for elem in self.finite_fixpoint_domains[relation_symbol]
            )
        else:
            for var, sort in zip(smt_input_vars, relation_symbol.input_sorts):
                carrier = self.interpret_sort(sort)
                rank_invariant = carrier.universally_quantify(var, rank_invariant)

        return smt.And(non_negative_constraint, rank_invariant)


class FOProvableStructureTemplate(UninterpretedStructureTemplate):
    """
    A structure such that in a theory with fixpoint definitions,
    if a formula phi is FO-provable with <unfold_depth> unfoldings of the
    fixpoint definitions, then the structure satisfies phi.
    """

    def __init__(self, theory: Theory, unfold_depth: int):
        assert unfold_depth >= 0

        super().__init__(theory.language)

        self.theory = theory

        # unfold LFP definitions
        overrides = OrderedDict()

        if unfold_depth != 0:
            for definition in theory.get_fixpoint_definitions():
                unfolded_definition = definition.unfold_definition(unfold_depth - 1)
                overrides[definition.relation_symbol] = \
                    self.interpret_fixpoint_definition(unfolded_definition)

        self.relation_interpretations.update(overrides)

    def get_constraint(self) -> smt.SMTTerm:
        # NOTE: fixpoint axioms are not included here

        constraint = smt.TRUE()
        for axiom in self.theory.get_axioms():
            constraint = smt.And(axiom.formula.interpret(self, {}), constraint)
        
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
