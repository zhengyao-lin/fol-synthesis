from __future__ import annotations

from typing import Dict, Optional, Tuple, Any, Callable, Set, Mapping, Union, Generator, Iterator
from dataclasses import dataclass, field

import itertools
import time
from contextlib import contextmanager

import z3
from z3 import ArithRef, BoolRef, Context, ModelRef, FuncDeclRef, AstRef, SortRef


@dataclass
class Z3Environment:
    context: Optional[Context]


@dataclass
class Language:
    """
    Unsorted language
    """
    functions: Dict[str, int] = field(default_factory=lambda: {}) # symbol -> arity
    relations: Dict[str, int] = field(default_factory=lambda: {}) # symbol -> arity

    def get_max_function_arity(self) -> int:
        return max(self.functions.values()) if len(self.functions) else 0

    def get_max_relation_arity(self) -> int:
        return max(self.relations.values()) if len(self.relations) else 0

    def expand(self, functions: Dict[str, int], relations: Dict[str, int]) -> Language:
        return Language({ **self.functions, **functions }, { **self.relations, **relations })


@dataclass
class Structure:
    """
    Structure of an unsorted language
    """
    universe_sort: SortRef
    language: Language
    function_interprets: Dict[str, Callable[..., AstRef]]
    relation_interprets: Dict[str, Callable[..., BoolRef]]

    def eval_function(self, symbol: str, arguments: Tuple[AstRef, ...]) -> AstRef:
        assert symbol in self.function_interprets, \
               f"function {symbol} not found"
        return self.function_interprets[symbol](*arguments)

    def eval_relation(self, symbol: str, arguments: Tuple[AstRef, ...]) -> BoolRef:
        assert symbol in self.relation_interprets, \
               f"relation {symbol} not found"
        return self.relation_interprets[symbol](*arguments)


@dataclass
class FiniteConcreteStructure(Structure):
    universe: Optional[Set[int]]

    FunctionMapping = Union[int, Dict[int, int], Dict[Tuple[int, ...], int]]
    RelationMapping = Union[Set[int], Set[Tuple[int, ...]]]

    @staticmethod
    def get_function_macro_from_concrete_mapping(mapping: FunctionMapping) -> Callable[..., ArithRef]:
        def macro(*arguments: ArithRef) -> ArithRef:
            if isinstance(mapping, int):
                assert len(arguments) == 0
                return mapping

            result = 0
            for key, value in mapping.items():
                if isinstance(key, int):
                    assert len(arguments) == 1
                    condition = arguments[0] == key
                else:
                    assert len(arguments) == len(key)
                    condition = z3.And(*(v1 == v2 for v1, v2 in zip(arguments, key)))

                result = z3.If(condition, value, result)

            return result
        return macro

    @staticmethod
    def get_relation_macro_from_concrete_set(relation: RelationMapping) -> Callable[..., BoolRef]:
        def macro(*arguments: ArithRef) -> BoolRef:
            result = False
            for value in relation:
                if isinstance(value, int):
                    assert len(arguments) == 1
                    condition = arguments[0] == value
                else:
                    assert len(arguments) == len(value)
                    condition = z3.And(*(v1 == v2 for v1, v2 in zip(arguments, value)))

                result = z3.If(condition, True, result)
            return result
        return macro

    @staticmethod
    def create(
        env: Z3Environment,
        language: Language,
        universe: Tuple[int, ...],
        functions: Dict[str, Union[FunctionMapping, Callable[..., ArithRef]]],
        relations: Dict[str, Union[RelationMapping, Callable[..., BoolRef]]],
    ):
        """
        Make a finite and concrete structure as a subset of int
        """
        universe_sort = z3.IntSort(env.context)

        # TODO: do something with the universe

        universe_size = len(universe)
        parsed_functions = {}
        parsed_relations = {}

        for symbol, arity in language.functions.items():
            assert symbol in functions, \
                   f"interpretation for {symbol} not given"

            if callable(functions[symbol]):
                parsed_functions[symbol] = functions[symbol]
                continue

            if isinstance(functions[symbol], int):
                assert arity == 0
            else:
                assert len(functions[symbol]) == universe_size ** arity, \
                       f"partially defined function for {symbol}"

            parsed_functions[symbol] = FiniteConcreteStructure.get_function_macro_from_concrete_mapping(functions[symbol])

        for symbol, arity in language.relations.items():
            assert symbol in relations, \
                   f"interpretation for {symbol} not given"

            if callable(relations[symbol]):
                parsed_relations[symbol] = relations[symbol]
                continue

            parsed_relations[symbol] = FiniteConcreteStructure.get_relation_macro_from_concrete_set(relations[symbol])

        return FiniteConcreteStructure(universe_sort, language, parsed_functions, parsed_relations, universe)


@dataclass
class FiniteSymbolicStructure(Structure):
    universe: Tuple[ArithRef, ...]
    function_overrides: Tuple[str, ...] = ()
    relation_overrides: Tuple[str, ...] = ()

    # TODO: add constraint saying that it's not
    # isomorphic to any of the existing models

    def iterate_universe(self, arity: int) -> Iterator[Tuple[ArithRef, ...]]:
        return itertools.product(self.universe, repeat=arity)

    def get_constraints(self) -> BoolRef:
        """
        Get a constraint saying that the model is well-formed
        """

        constraints = [] # [ z3.Distinct(*self.universe) ]

        for function_name, arity in self.language.functions.items():
            if function_name not in self.function_overrides:
                function = self.function_interprets[function_name]
                constraints.append(z3.And(*(
                    z3.Or(*(function(*args) == var for var in self.universe))
                    for args in self.iterate_universe(arity)
                )))

        return z3.And(*constraints)

    def interpret_z3_model(self, model: ModelRef) -> Structure:
        """
        Obtain a concrete structure from the given z3 model
        """
        universe: Set[int] = set()
        functions: Dict[str, Callable[..., ArithRef]] = {}
        relations: Dict[str, Callable[..., BoolRef]] = {}

        for var in self.universe:
            universe.add(model[var].as_long())

        for function_name, arity in self.language.functions.items():
            if function_name in self.function_overrides:
                functions[function_name] = self.function_interprets[function_name]
            else:
                declaration = self.function_interprets[function_name]

                if arity == 0 and model[declaration()] is None:
                    # just pick anything from the domain
                    function = model[self.universe[0]]
                else:
                    function = (lambda decl: lambda *args: model.eval(decl(*args)))(declaration)

                functions[function_name] = function

        for relation_name in self.language.relations:
            if relation_name in self.relation_overrides:
                relations[relation_name] = self.relation_interprets[relation_name]
            else:
                declaration = self.relation_interprets[relation_name]

                if model[declaration] is None:
                    relation = lambda *args: False
                else:
                    relation = (lambda decl: lambda *args: model.eval(decl(*args)))(declaration)

                relations[relation_name] = relation

        return FiniteConcreteStructure(z3.IntSort(), self.language, functions, relations, universe)

    @staticmethod
    def create(
        env: Z3Environment,
        language: Language,
        domain_size: int,
        function_overrides: Dict[str, Callable[..., ArithRef]] = {},
        relation_overrides: Dict[str, Callable[..., BoolRef]] = {},
    ):
        """
        1. Generate <domain_size> Int variables, functions, and relations
        2. State that they are disjoint
        3. For each function, state that they are closed within the domain
        """

        domain_vars = tuple(z3.FreshInt(ctx=env.context) for _ in range(domain_size))
        functions: Dict[str, Callable[..., ArithRef]] = function_overrides.copy()
        relations: Dict[str, Callable[..., BoolRef]] = relation_overrides.copy()

        for function_name, arity in language.functions.items():
            if function_name in functions:
                continue

            if arity == 0:
                function = (lambda i: lambda: i)(z3.FreshInt(ctx=env.context))
            else:
                function = z3.FreshFunction(*(z3.IntSort() for _ in range(arity)), z3.IntSort())
            
            functions[function_name] = function

        
        for relation_name, arity in language.relations.items():
            if relation_name in relations:
                continue

            relations[relation_name] = z3.FreshFunction(*(z3.IntSort() for _ in range(arity)), z3.BoolSort())

        return FiniteSymbolicStructure(
            z3.IntSort(), language, functions, relations,
            universe=domain_vars,
            function_overrides=tuple(function_overrides.keys()),
            relation_overrides=tuple(relation_overrides.keys()),
        )


class ControlVariable:
    """
    A list of boolean variables reprensenting a non-negative integer
    in the range [0, <num_options>)
    """

    counter = 0

    def __init__(self, env: Z3Environment, num_options: int):
        # find the number of bits required
        self.num_bits = (num_options - 1).bit_length()
        self.num_options = num_options
        self.control_var = z3.BitVec(f"cv{ControlVariable.counter}", self.num_bits, env.context)
        ControlVariable.counter += 1

    def get_equality_constraint(self, num: int) -> BoolRef:
        """
        Generate a constraint saying that the variable equals to the given constant
        """
        return self.control_var == z3.BitVecVal(num, self.num_bits)

    def dismiss_z3_model(self, model: ModelRef) -> BoolRef:
        return z3.Not(self.get_equality_constraint(self.interpret_z3_model(model)))

    def interpret_z3_model(self, model: ModelRef) -> int:
        value = model[self.control_var].as_long()
        assert value < self.num_options, "invalid model"
        return value


class TermVariable:
    """
    An undetermined term

    Suppose the number of variables is n

    case control_var of
        0 => null
        n + m + 1 => the m^th function symbol
        i + 1 (i < n) => the i^th variable
    """

    def __init__(self, env: Z3Environment, language: Language, depth: int, num_vars: int):
        assert depth >= 0 and num_vars >= 0

        self.functions = tuple(language.functions.items())
        self.depth = depth
        self.num_vars = num_vars
        self.control_var = ControlVariable(env, 1 + self.num_vars + len(self.functions))

        if depth == 0:
            self.subterms = ()
        else:
            self.subterms = tuple(TermVariable(env, language, depth - 1, num_vars) for _ in range(language.get_max_function_arity()))

    def get_is_null_constraint(self) -> BoolRef:
        """
        Return a constraint saying that the term is "null"
        needed when the parent doesn't need this subterm
        """
        return z3.And(self.control_var.get_equality_constraint(0), *(subterm.get_is_null_constraint() for subterm in self.subterms))

    def get_arity_of_control_value(self, val: int) -> int:
        if val <= self.num_vars:
            num_subterms = 0
        else:
            _, num_subterms = self.functions[val - self.num_vars - 1]
        return num_subterms

    def get_function_symbol_of_control_value(self, val: int) -> str:
        assert val >= self.num_vars + 1
        symbol, _ = self.functions[val - self.num_vars - 1]
        return symbol

    def get_well_formedness_constraint(self) -> BoolRef:
        """
        Return a contraint saying that the term is well-formed
        """

        wff_constraint = False

        # if the node is a variable, we don't need any subterms
        for i in range(1, 1 + self.num_vars + len(self.functions)):
            arity = self.get_arity_of_control_value(i)

            if arity != 0 and self.depth == 0:
                continue

            # the first <arity> subterms are well-formed
            # and the rest is null
            wff_constraint = z3.If(
                self.control_var.get_equality_constraint(i),
                z3.And(
                    z3.And(*(subterm.get_well_formedness_constraint() for subterm in self.subterms[:arity])),
                    z3.And(*(subterm.get_is_null_constraint() for subterm in self.subterms[arity:]))
                ),
                wff_constraint,
            )

        return wff_constraint

    def eval(self, structure: Structure, assignment: Tuple[AstRef, ...]) -> AstRef:
        """
        Evaluate the term given a structure and assignment to the free variables
        """

        result = z3.FreshConst(structure.universe_sort, "undef")

        # if the node is a variable, we don't need any subterms
        for i in range(1, 1 + self.num_vars + len(self.functions)):
            if i <= self.num_vars:
                case_result = assignment[i - 1]
            else:
                symbol = self.get_function_symbol_of_control_value(i)
                arity = self.get_arity_of_control_value(i)

                if arity != 0 and self.depth == 0:
                    continue

                subterm_results = tuple(subterm.eval(structure, assignment) for subterm in self.subterms[:arity])
                case_result = structure.eval_function(symbol, subterm_results)

            result = z3.If(self.control_var.get_equality_constraint(i), case_result, result)

        return result

    def eval_z3_model(self, model: ModelRef, structure: Structure, assignment: Tuple[AstRef, ...]) -> BoolRef:
        """
        Given a z3 model, the formula is fixed, but we can still evaluate it on some structure and assignment
        """

        control_val = self.control_var.interpret_z3_model(model)
        assert control_val != 0

        if control_val <= self.num_vars:
            return assignment[control_val - 1]
        else:
            symbol = self.get_function_symbol_of_control_value(control_val)
            arity = self.get_arity_of_control_value(control_val)

            subterm_results = tuple(subterm.eval_z3_model(model, structure, assignment) for subterm in self.subterms[:arity])
            return structure.eval_function(symbol, subterm_results)

    def dismiss_z3_model(self, model: ModelRef) -> BoolRef:
        """
        Get a constraint to rule out this particular model
        """
        return z3.Or(
            self.control_var.dismiss_z3_model(model),
            *(
                subterm.dismiss_z3_model(model)
                for subterm in self.subterms
            ),
        )

    def unparse_z3_model(self, model: ModelRef) -> str:
        """
        Unparse a term from the given model
        """
        control_val = self.control_var.interpret_z3_model(model)

        assert 1 <= control_val <= self.num_vars + len(self.functions), \
               f"not a model of the well-formedness constraint: {model}"

        if control_val <= self.num_vars:
            return f"x{control_val - 1}"
        else:
            symbol = self.get_function_symbol_of_control_value(control_val)
            arity = self.get_arity_of_control_value(control_val)

            if arity == 0:
                return symbol

            subterm_strings = []

            for subterm in self.subterms[:arity]:
                subterm_strings.append(subterm.unparse_z3_model(model))

            return f"{symbol}({', '.join(subterm_strings)})"


class AtomicFormulaVariable:
    """
    An undetermined atomic formula

    case control_var of
        0 => false
        1 => true
        2 => equality
        n + 3 => the n^th relation
    """

    def __init__(self, env: Z3Environment, language: Language, term_depth: int, num_vars: int, allow_equality: bool = False):
        self.relations = tuple(language.relations.items())
        self.allow_equality = allow_equality
        self.control_var = ControlVariable(env, 3 + len(self.relations))
        # we need at least 2 arguments since we have equality
        self.arguments = tuple(TermVariable(env, language, term_depth, num_vars) for _ in range(max(2, language.get_max_relation_arity())))

    def get_well_formedness_constraint(self) -> BoolRef:
        constraint = \
            z3.If(
                z3.Or(
                    self.control_var.get_equality_constraint(0),
                    self.control_var.get_equality_constraint(1),
                ),
                z3.And(*(argument.get_is_null_constraint() for argument in self.arguments)),
            z3.If(
                # constraints for equality well-formedness
                self.control_var.get_equality_constraint(2),
                z3.And(
                    z3.And(*(argument.get_well_formedness_constraint() for argument in self.arguments[:2])),
                    z3.And(*(argument.get_is_null_constraint() for argument in self.arguments[2:])),
                ) if self.allow_equality else False,
                False,
            ))

        for i, (_, arity) in enumerate(self.relations, 3):
            constraint = z3.If(
                self.control_var.get_equality_constraint(i),
                z3.And(
                    z3.And(*(argument.get_well_formedness_constraint() for argument in self.arguments[:arity])),
                    z3.And(*(argument.get_is_null_constraint() for argument in self.arguments[arity:])),
                ),
                constraint,
            )

        return constraint

    def get_is_constant_constraint(self, value: bool) -> BoolRef:
        return z3.And(
            self.control_var.get_equality_constraint(1),
            *(argument.get_is_null_constraint() for argument in self.arguments),
        ) if value else z3.And(
            self.control_var.get_equality_constraint(0),
            *(argument.get_is_null_constraint() for argument in self.arguments),
        )

    def eval(self, structure: Structure, assignment: Tuple[AstRef, ...]) -> BoolRef:
        """
        Evaluate an formula to a boolean value in z3
        """

        result = \
            z3.If(
                self.control_var.get_equality_constraint(0),
                False,
            z3.If(
                self.control_var.get_equality_constraint(1),
                True,
            z3.If(
                self.control_var.get_equality_constraint(2),
                self.arguments[0].eval(structure, assignment) == self.arguments[1].eval(structure, assignment),
                False,
            )))

        for i, (symbol, arity) in enumerate(self.relations, 3):
            arguments = tuple(argument.eval(structure, assignment) for argument in self.arguments[:arity])
            result = z3.If(
                self.control_var.get_equality_constraint(i),
                structure.eval_relation(symbol, arguments),
                result,
            )

        return result

    def eval_z3_model(self, model: ModelRef, structure: Structure, assignment: Tuple[AstRef, ...]) -> BoolRef:
        control_val = self.control_var.interpret_z3_model(model)

        if control_val == 0:
            return False
        elif control_val == 1:
            return True
        elif control_val == 2:
            return self.arguments[0].eval_z3_model(model, structure, assignment) == \
                   self.arguments[1].eval_z3_model(model, structure, assignment)

        symbol, arity = self.relations[control_val - 3]
        arguments = tuple(argument.eval_z3_model(model, structure, assignment) for argument in self.arguments[:arity])

        return structure.eval_relation(symbol, arguments)

    def dismiss_z3_model(self, model: ModelRef) -> BoolRef:
        """
        Get a constraint to rule out this particular model
        """
        return z3.Or(
            self.control_var.dismiss_z3_model(model),
            *(
                argument.dismiss_z3_model(model)
                for argument in self.arguments
            ),
        )

    def unparse_z3_model(self, model: ModelRef) -> str:
        """
        Unparse a formula from the given model
        """

        control_val = self.control_var.interpret_z3_model(model)

        assert 0 <= control_val <= 3 + len(self.relations), \
               f"not a model of the well-formedness constraint: {model}"

        if control_val == 0:
            return "⊥"
        elif control_val == 1:
            return "⊤"
        elif control_val == 2:
            return f"{self.arguments[0].unparse_z3_model(model)} = {self.arguments[1].unparse_z3_model(model)}"

        symbol, arity = self.relations[control_val - 3]

        if arity == 0:
            return symbol

        argument_stings = tuple(argument.unparse_z3_model(model) for argument in self.arguments[:arity])

        return f"{symbol}({', '.join(argument_stings)})"


class HornClauseSynthesizer:
    """
    Synthesize (universally quantified) horn clauses in the given language
    that are correct in a set of examples but not valid in FO-semantics
    """

    def __init__(
        self,
        env: Z3Environment,
        language: Language,
        hypothesis_term_depth: int,
        conclusion_term_depth: int,
        max_num_vars: int,
        max_num_hypotheses: int,
        min_num_hypotheses: int = 0,
        allow_equality_in_conclusion: bool = False,
    ):
        self.env = env
        self.language = language
        self.hypothesis_term_depth = hypothesis_term_depth
        self.conclusion_term_depth = conclusion_term_depth
        self.max_num_vars = max_num_vars
        self.min_num_hypotheses = min_num_hypotheses
        self.max_num_hypotheses = max_num_hypotheses
        self.previous_models = []

        self.syn_counterexample: Optional[Structure] = None
        self.ver_counterexample: Optional[FiniteSymbolicStructure] = None
        self.ver_assignment: Optional[Tuple[ArithRef, ...]] = None # assignment to free vars
        
        # one solver for synthesis and another for verification
        self.syn_solver = z3.Solver(ctx=env.context)
        self.ver_solver = z3.Solver(ctx=env.context)

        self.hypotheses = tuple(
            AtomicFormulaVariable(self.env, language, hypothesis_term_depth, max_num_vars, allow_equality=False)
            for _ in range(max_num_hypotheses)
        )
        self.conclusion = AtomicFormulaVariable(self.env, language, conclusion_term_depth, max_num_vars, allow_equality=allow_equality_in_conclusion)

        # add well-formedness constraints
        for hyp in self.hypotheses:
            self.add_synthesis_constraint(hyp.get_well_formedness_constraint())
        self.add_synthesis_constraint(self.conclusion.get_well_formedness_constraint())

    def add_common_constraint(self, constraint: BoolRef) -> None:
        self.syn_solver.add(constraint)
        self.ver_solver.add(constraint)

    def add_synthesis_constraint(self, constraint: BoolRef) -> None:
        self.syn_solver.add(constraint)

    def add_verification_constraint(self, constraint: BoolRef) -> None:
        self.ver_solver.add(constraint)

    def eval_formula_with_z3_model(self, model: ModelRef, structure: Structure, assignment: Tuple[AstRef, ...]) -> BoolRef:
        """
        The formula is fixed by the given z3 model, then evaluate such formula on the given structure
        """
        return z3.Implies(
            z3.And(*(
                hyp.eval_z3_model(model, structure, assignment)
                for hyp in self.hypotheses
            )),
            self.conclusion.eval_z3_model(model, structure, assignment),
        )

    def eval_formula(self, structure: Structure, assignment: Tuple[AstRef, ...]) -> BoolRef:
        """
        Evaluate the undetermined formula on the given structure
        """
        return z3.Implies(
            z3.And(*(
                hyp.eval(structure, assignment)
                for hyp in self.hypotheses
            )),
            self.conclusion.eval(structure, assignment),
        )

    def add_example(self, example: Structure) -> None:
        assert example.universe is not None, "examples have to be concrete"

        for assignment in itertools.product(*([example.universe] * self.max_num_vars)):
            self.add_synthesis_constraint(z3.Implies(
                z3.And(*(hyp.eval(example, assignment) for hyp in self.hypotheses)),
                self.conclusion.eval(example, assignment),
            ))
    
    def set_synthesis_counterexample(self, counterexample: Structure, assignment: Tuple[ArithRef, ...]) -> None:
        self.add_synthesis_constraint(z3.Not(self.eval_formula(counterexample, assignment)))
        self.syn_counterexample = counterexample

    def set_verification_counterexample(self, counterexample: FiniteSymbolicStructure) -> None:
        self.ver_counterexample = counterexample
        self.add_verification_constraint(counterexample.get_constraints())

        assignment = []

        for _ in range(self.max_num_vars):
            var = z3.FreshInt()
            self.add_verification_constraint(z3.Or(*(
                var == domain_var
                for domain_var in counterexample.universe
            )))
            assignment.append(var)
        
        self.ver_assignment = tuple(assignment)

    def dismiss_model(self, model: ModelRef) -> None:
        counterexample = self.syn_counterexample
        assert counterexample is not None

        assignment = tuple(z3.FreshInt(ctx=self.env.context) for _ in range(self.max_num_vars))
        self.add_synthesis_constraint(
            z3.ForAll(assignment, self.eval_formula_with_z3_model(model, counterexample, assignment)),
        )

    def dismiss_previous_models(self) -> None:
        counterexample = self.syn_counterexample
        assert counterexample is not None

        # require that any new formula is not implied by existing ones
        # even after permutation of variables
        assignment = tuple(z3.FreshInt(ctx=self.env.context) for _ in range(self.max_num_vars))

        for permutation in itertools.permutations(assignment):
            previous_formulas = z3.And(*(
                self.eval_formula_with_z3_model(model, counterexample, permutation)
                for model in self.previous_models
            ))

            self.add_synthesis_constraint(z3.Not(z3.Implies(
                previous_formulas,
                self.eval_formula(counterexample, assignment),
            )))

    @contextmanager
    def push_synthesis_solver(self) -> Generator[None, None, None]:
        try:
            self.syn_solver.push()
            yield
        finally:
            self.syn_solver.pop()

    @contextmanager
    def push_verification_solver(self) -> Generator[None, None, None]:
        try:
            self.ver_solver.push()
            yield
        finally:
            self.ver_solver.pop()

    def print_finite_structure(self, structure: FiniteConcreteStructure) -> None:
        print(f"universe: {structure.universe}")

        for function_name, arity in structure.language.functions.items():
            print(f"function {function_name}:")
            for args in itertools.product(structure.universe, repeat=arity):
                print(f" - {args} |-> {structure.eval_function(function_name, args)}")

        for relation_name, arity in structure.language.relations.items():
            print(f"relation {relation_name}:")
            for args in itertools.product(structure.universe, repeat=arity):
                if structure.eval_relation(relation_name, args):
                    print(f" - {args}")

    def unparse_z3_model(self, model: ModelRef) -> str:
        hypothesis_strings = tuple(hyp.unparse_z3_model(model) for hyp in self.hypotheses)
        hypothesis_strings = tuple(hyp for hyp in hypothesis_strings if hyp != "⊤")
        hypothesis_string = " /\\ ".join(hypothesis_strings)
        conclusion_string = self.conclusion.unparse_z3_model(model)

        if len(hypothesis_strings):
            return f"{hypothesis_string} => {conclusion_string}"
        else:
            return f"{conclusion_string}"

    def synthesize(self) -> Generator[str, None, None]:
        assert self.syn_counterexample is not None and \
               self.ver_counterexample is not None

        for num_hypotheses in range(self.min_num_hypotheses, self.max_num_hypotheses + 1):
            print(f"synthesizing formulas with {num_hypotheses} hypothesis(es)")
            while True:
                begin = time.time()

                # Step 1: synthesis
                with self.push_synthesis_solver():
                    # self.dismiss_previous_models()

                    # force the number of hypotheses
                    for hyp in self.hypotheses[num_hypotheses:]:
                        self.add_synthesis_constraint(hyp.get_is_constant_constraint(True))

                    if self.syn_solver.check() != z3.sat:
                        print(f"no more valid formulas with {num_hypotheses} hypothesis(es), elapsed: {round(time.time() - begin, 2)}s")
                        break

                    model = self.syn_solver.model()

                formula_string = self.unparse_z3_model(model)
                print(f"verifying {formula_string}", end="", flush=True)

                # Step 2: verification
                # check if the generated model is valid among verification structures
                with self.push_verification_solver():
                    self.add_verification_constraint(
                        z3.Not(self.eval_formula_with_z3_model(model, self.ver_counterexample, self.ver_assignment)),
                    )
                    
                    result = self.ver_solver.check()

                    if result == z3.sat:
                        ver_model = self.ver_solver.model()
                        counterexample = self.ver_counterexample.interpret_z3_model(ver_model)
                        # self.print_finite_structure(counterexample)
                        self.add_example(counterexample)
                        print(f" - rejected, elapsed {round(time.time() - begin, 2)}s")
                    else:
                        assert result == z3.unsat
                        self.previous_models.append(model)
                        self.dismiss_model(model)
                        print(f" - accepted, elapsed {round(time.time() - begin, 2)}s")
                        yield formula_string
