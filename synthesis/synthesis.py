from typing import Any, Generic, TypeVar, Tuple, Mapping, Dict, Generator, List

from dataclasses import dataclass
from abc import ABC, abstractmethod
from contextlib import contextmanager

import itertools

from synthesis import smt

from .fol import *
from .template import Template


class BoundedIntegerVariable(Template[int]):
    """
    An integer variable with range lower upper
    """

    def __init__(self, lower: int, upper: int):
        assert upper >= lower
        self.lower = lower
        self.upper = upper
        self.variable = smt.FreshSymbol(smt.INT)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(smt.LE(smt.Int(self.lower), self.variable), smt.LE(self.variable, smt.Int(self.upper)))

    def get_from_smt_model(self, model: smt.SMTModel) -> int:
        return model[self.variable].constant_value() # type: ignore

    def equals(self, value: int) -> smt.SMTTerm:
        return smt.Equals(self.variable, smt.Int(value))


class TermVariable(Term):
    """
    Template for a term
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], depth: int, sort: Optional[Sort] = None):
        self.language = language
        self.free_vars = free_vars
        self.depth = depth
        self.sort = sort

        self.node = BoundedIntegerVariable(0, len(self.free_vars) + len(self.language.function_symbols))

        if depth != 0:
            self.subterms = tuple(TermVariable(language, self.free_vars, depth - 1) for _ in range(language.get_max_function_arity()))
        else:
            self.subterms = ()

    def get_free_variables(self) -> Set[Variable]:
        return set(self.free_vars)

    def substitute(self, substitution: Mapping[Variable, Term]) -> Term:
        raise NotImplementedError()

    def get_constraint(self) -> smt.SMTTerm:
        """
        The term can be of any sort
        """
        return smt.Or(*(self.get_well_formedness_constraint(sort) for sort in self.language.sorts))

    def get_from_smt_model(self, model: smt.SMTModel) -> Term:
        """
        Get a concrete term from the given model
        """
        node_value = self.node.get_from_smt_model(model)
        assert node_value != 0, f"unexpected node value {node_value}"

        if node_value <= len(self.free_vars):
            return self.free_vars[node_value - 1]
        else:
            symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
            arity = len(symbol.input_sorts)
            return Application(symbol, tuple(subterm.get_from_smt_model(model) for subterm in self.subterms[:arity]))

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

        return smt.And(constraint, self.node.get_constraint())

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        assert self.sort is not None, \
               f"term variable does not have a specific sort"
        return self.interpret_as_sort(self.sort, structure, valuation)

    def interpret_as_sort(self, sort: Sort, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
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
                        subterm.interpret_as_sort(subterm_sort, structure, valuation)
                        for subterm_sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])
                    )
                    interp = smt.Ite(self.node.equals(node_value), structure.interpret_function(symbol, *arguments), interp)

        return interp


class AtomicFormulaVariable(Formula):
    """
    Template for an atomic formula (i.e. false, true, or other relations)
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], term_depth: int):
        self.language = language
        self.free_vars = free_vars
        self.term_depth = term_depth
        self.node = BoundedIntegerVariable(0, 2 + len(language.relation_symbols))

        self.subterms = tuple(TermVariable(language, free_vars, term_depth) for _ in range(language.get_max_relation_arity()))

    def __str__(self) -> str:
        return f"<φ({', '.join(map(str, self.free_vars))}), depth {self.term_depth}>"

    def get_free_variables(self) -> Set[Variable]:
        return set(self.free_vars)

    def substitute(self, substitution: Mapping[Variable, Term]) -> Formula:
        raise NotImplementedError()

    def get_constraint(self) -> smt.SMTTerm:
        return self.get_well_formedness_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> AtomicFormula:
        """
        Get a concrete atomic formula from the model
        """
        node_value = self.node.get_from_smt_model(model)

        if node_value == 0:
            return Falsum()
        elif node_value == 1:
            return Verum()
        else:
            symbol = self.language.relation_symbols[node_value - 2]
            arity = len(symbol.input_sorts)
            return RelationApplication(symbol, tuple(subterm.get_from_smt_model(model) for subterm in self.subterms[:arity]))

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

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
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
                    subterm.interpret_as_sort(sort, structure, valuation)
                    for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])
                )
                interp = smt.Ite(self.node.equals(node_value), structure.interpret_relation(symbol, *arguments), interp)

        return interp


class ModelVariable(Template[Structure], Structure):
    """
    A model variable can act as a structure, i.e. a formula can be
    interpreted in it, but at the same time it can be used as
    a template to synthesize an actual concrete model
    """


class UninterpretedModelVariable(SymbolicStructure, ModelVariable):
    """
    A structure in which all uninterpreted sorts are assigned
    the carrier <default_sort> and all uninterpreted functions/relations
    are assigned uninterpreted SMT functions
    """

    def __init__(self, language: Language, default_sort: smt.SMTSort):
        carriers: Dict[Sort, CarrierSet] = {}
        function_interpretations: Dict[FunctionSymbol, smt.SMTFunction] = {}
        relation_interpretations: Dict[RelationSymbol, smt.SMTFunction] = {}

        for sort in language.sorts:
            if sort.smt_hook is None:
                carriers[sort] = RefinementCarrierSet(default_sort)

        for function_symbol in language.function_symbols:
            if function_symbol.smt_hook is None:
                smt_input_sorts = tuple(sort.smt_hook or default_sort for sort in function_symbol.input_sorts)
                smt_output_sort = function_symbol.output_sort.smt_hook or default_sort
                function_interpretations[function_symbol] = smt.FreshFunction(smt_input_sorts, smt_output_sort)

        for relation_symbol in language.relation_symbols:
            if relation_symbol.smt_hook is None:
                smt_input_sorts = tuple(sort.smt_hook or default_sort for sort in relation_symbol.input_sorts)
                relation_interpretations[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.BOOL)

        super().__init__(language, carriers, function_interpretations, relation_interpretations)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.TRUE()

    def get_from_smt_model(self, model: smt.SMTModel) -> Structure:
        """
        Concretize all functions
        """
        concrete_functions = {}
        concrete_relations = {}

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

        return SymbolicStructure(self.theory.language, self.carriers, concrete_functions, concrete_relations)

    def equals(self, value: Structure) -> smt.SMTTerm:
        raise NotImplementedError()


class FiniteLFPModelVariable(UninterpretedModelVariable):
    """
    A variable/template for a LFP model of a given theory
    in which all interpreted sorts have finite domains
    """

    def __init__(self, theory: Theory, size_bounds: Mapping[Sort, int]):
        super().__init__(theory.language, smt.INT)

        self.theory = theory
        self.rank_functions: Dict[RelationSymbol, smt.SMTFunction] = {}

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

        # for any fixpoint definition, add a rank function
        for sentence in theory.sentences:
            if isinstance(sentence, FixpointDefinition):
                relation_symbol = sentence.relation_symbol
                assert relation_symbol not in self.rank_functions, \
                       f"duplicate fixpoint definition for {relation_symbol}"
                smt_input_sorts = tuple(sort.smt_hook or smt.INT for sort in relation_symbol.input_sorts)
                self.rank_functions[relation_symbol] = smt.FreshFunction(smt_input_sorts, smt.INT)

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
                constraint = smt.And(self.get_constraints_for_least_fixpoint(sentence), constraint)
            else:
                assert False, f"unsupported sentence {sentence}"

        return constraint

    def get_constraints_for_least_fixpoint(self, definition: FixpointDefinition) -> smt.SMTTerm:
        """
        Return a constraint saying that the structure satisfies the given fixpoint definition (as least fixpoint)
        """
        
        # enforcing fixpoint
        constraint = definition.as_formula().interpret(self, {})

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

        constraint = smt.And(rank_invariant, constraint)

        return constraint

    def get_from_smt_model(self, model: smt.SMTModel) -> Structure:
        """
        Get a concrete finite structure
        """

        uninterp_structure = super().get_from_smt_model(model)

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
                        uninterp_structure.interpret_function(symbol, *args))(function_symbol)

        # construct new relation interpretations
        for relation_symbol in self.theory.language.relation_symbols:
            if relation_symbol.smt_hook is None:
                concrete_relations[relation_symbol] = \
                    (lambda symbol: lambda *args: \
                        uninterp_structure.interpret_relation(symbol, *args))(relation_symbol)

        return SymbolicStructure(self.theory.language, concrete_carriers, concrete_functions, concrete_relations)


class FOProvableModelVariable(UninterpretedModelVariable):
    """
    A structure such that in a theory with fixpoint definitions,
    if a formula phi is FO-provable with <unfold_depth> unfoldings of the
    fixpoint definitions, then the structure satisfies phi.
    """

    def __init__(self, theory: Theory, unfold_depth: int):
        super().__init__(theory.language, smt.INT)

        self.theory = theory

        # unfold LFP definitions
        overrides = {}
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
        valuation = {
            var: smt.FreshSymbol(self.get_smt_sort(var.sort))
            for var in definition.variables
        }
        smt_formula = definition.definition.interpret(self, valuation)

        def interp(*args: smt.SMTTerm) -> smt.SMTTerm:
            assert len(args) == len(definition.variables)
            substitution = { valuation[k]: v for k, v in zip(definition.variables, args) }
            return smt_formula.substitute(substitution) # substitution on the SMT formula

        return interp


class CEIGSynthesizer:
    """
    Synthesize formulas that are valid in some class of models
    but not always true in some other class
    """

    @contextmanager
    def solver_push(self, solver: smt.SMTSolver) -> Generator[None, None, None]:
        try:
            solver.push()
            yield
        finally:
            solver.pop()

    def synthesize_for_model_classes(
        self,
        templates: Tuple[Formula, ...],
        trivial_model: ModelVariable,
        goal_model: ModelVariable,
        *_,
        solver_name: str = "z3",
    ) -> Generator[Formula, None, None]:
        """
        Given a class of models C_1 (described by <trivial_model>)
        and another class of models C_2 (described by <goal_model>)
        Synthesize all formula phi (using each template in <templates> in sequence)
        such that
          - exists M in C_1, not (M |= phi)
          - forall M in C_2, M |= phi

        If the second condition is not true, the counterexample model M is
        added back to the first round as an additional constraint

        e.g. to synthesize formulas true in all bounded finite LFP models but not in all FO model,
        we can take C_1 to be FOProvableStructure and C_2 to be FiniteLFPModelVariable

        e.g. to synthesize formulas true in a FO theory T but not in a FO subtheory T'
        we can take C_1 to be FOProvableStructure(T') and C_2 to be FOProvableStructure(T)
        """

        counterexamples: List[Structure] = []
        synthesized_formulas: List[Formula] = []
        
        with smt.Solver(name=solver_name) as gen_solver, \
             smt.Solver(name=solver_name) as check_solver: # to check that the synthesized formulas are valid

            gen_solver.add_assertion(trivial_model.get_constraint())
            check_solver.add_assertion(goal_model.get_constraint())

            for template in templates:
                print(f"### synthesizing formulas of the form {template}")

                with self.solver_push(gen_solver):
                    gen_solver.add_assertion(template.get_constraint())

                    # add all existing counterexamples
                    for counterexample in counterexamples:
                        gen_solver.add_assertion(template.quantify_all_free_variables().interpret(counterexample, {}))

                    # avoid duplicates for all existing formulas
                    for formula in synthesized_formulas:
                        gen_solver.add_assertion(formula.quantify_all_free_variables().interpret(trivial_model, {}))

                    # when negated, the (universally quantified) free variables
                    # become existentially quantified, we do skolemization here
                    free_vars = template.get_free_variables()
                    gen_skolem_constants = { # for the fo provable structure
                        v: trivial_model.interpret_sort(v.sort).get_fresh_constant(gen_solver, v.sort)
                        for v in free_vars
                    }
                    check_skolem_constants = { # for the counterexample
                        v: goal_model.interpret_sort(v.sort).get_fresh_constant(check_solver, v.sort)
                        for v in free_vars
                    }

                    # not valid in some trivial model
                    gen_solver.add_assertion(smt.Not(template.interpret(trivial_model, gen_skolem_constants)))

                    while gen_solver.solve():
                        candidate = template.get_from_smt_model(gen_solver.get_model())
                        print(candidate, "... ", end="", flush=True)

                        # check if the candidate is valid in all goal models
                        with self.solver_push(check_solver):
                            check_solver.add_assertion(smt.Not(candidate.interpret(goal_model, check_skolem_constants)))

                            if check_solver.solve():
                                # found counterexample
                                print("✘")
                                counterexample = goal_model.get_from_smt_model(check_solver.get_model())
                                counterexamples.append(counterexample)
                                gen_solver.add_assertion(template.quantify_all_free_variables().interpret(counterexample, {}))
                            else:
                                # no conuterexample found
                                print("✓")
                                yield candidate
                                synthesized_formulas.append(candidate)
                                gen_solver.add_assertion(candidate.quantify_all_free_variables().interpret(trivial_model, {}))
