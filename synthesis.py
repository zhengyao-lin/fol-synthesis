from typing import Dict, Optional, Tuple, Any, Callable, Set, Mapping, Union
from dataclasses import dataclass, field

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


@dataclass
class Structure:
    """
    Structure of an unsorted language
    """
    universe_sort: SortRef
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
    def from_finite_int(
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

            parsed_functions[symbol] = Structure.get_function_macro_from_concrete_mapping(functions[symbol])

        for symbol, arity in language.relations.items():
            assert symbol in relations, \
                   f"interpretation for {symbol} not given"

            if callable(relations[symbol]):
                parsed_relations[symbol] = relations[symbol]
                continue

            parsed_relations[symbol] = Structure.get_relation_macro_from_concrete_set(relations[symbol])

        return Structure(universe_sort, parsed_functions, parsed_relations)


class TermVariable:
    """
    An undetermined term

    Suppose the number of variables is n

    case control_var of
        -1 => null
        n + m => the m^th function symbol
        i (i < n) => the i^th variable
    """

    def __init__(self, env: Z3Environment, language: Language, depth: int, num_vars: int):
        assert depth >= 0 and num_vars >= 0

        self.functions = tuple(language.functions.items())
        self.depth = depth
        self.num_vars = num_vars
        self.control_var = z3.FreshInt("cv_term", env.context)

        if depth == 0:
            self.subterms = ()
        else:
            self.subterms = tuple(TermVariable(env, language, depth - 1, num_vars) for _ in range(language.get_max_function_arity()))

    def get_is_null_constraint(self) -> BoolRef:
        """
        Return a constraint saying that the term is "null"
        needed when the parent doesn't need this subterm
        """
        return z3.And(self.control_var == -1, *(subterm.get_is_null_constraint() for subterm in self.subterms))

    def get_number_subterms_for_control_value(self, val: int) -> int:
        if val < self.num_vars:
            num_subterms = 0
        else:
            _, num_subterms = self.functions[val - self.num_vars]
        return num_subterms

    def get_function_symbol_of_control_value(self, val: int) -> str:
        assert val >= self.num_vars
        symbol, _ = self.functions[val - self.num_vars]
        return symbol

    def get_well_formedness_constraint(self) -> BoolRef:
        """
        Return a contraint saying that the term is well-formed
        """

        if self.depth == 0:
            return z3.And(0 <= self.control_var, self.control_var < self.num_vars)

        # range_constraint = 0 <= self.control_var < self.num_vars + len(self.language.functions)
        wff_constraint = False

        # if the node is a variable, we don't need any subterms
        for i in range(self.num_vars + len(self.functions)):
            num_subterms = self.get_number_subterms_for_control_value(i)

            # the first <num_subterms> subterms are well-formed
            # and the rest is null
            wff_constraint = z3.If(
                self.control_var == i,
                z3.And(
                    z3.And(*(subterm.get_well_formedness_constraint() for subterm in self.subterms[:num_subterms])),
                    z3.And(*(subterm.get_is_null_constraint() for subterm in self.subterms[num_subterms:]))
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
        for i in range(self.num_vars + len(self.functions)):
            if i < self.num_vars:
                case_result = assignment[i]
            elif self.depth != 0:
                num_subterms = self.get_number_subterms_for_control_value(i)
                subterm_results = tuple(subterm.eval(structure, assignment) for subterm in self.subterms[:num_subterms])
                symbol = self.get_function_symbol_of_control_value(i)
                case_result = structure.eval_function(symbol, subterm_results)
            else:
                continue

            result = z3.If(self.control_var == i, case_result, result)

        return result

    def unparse_z3_model(self, model: ModelRef) -> str:
        """
        Unparse a term from the given model
        """
        control_val = model[self.control_var].as_long()

        assert 0 <= control_val <= self.num_vars + len(self.functions), \
               f"not a model of the well-formedness constraint: {model}"

        if control_val < self.num_vars:
            return f"x{control_val}"
        else:
            symbol, arity = self.functions[control_val - self.num_vars]
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

    def __init__(self, env: Z3Environment, language: Language, term_depth: int, num_vars: int):
        self.relations = tuple(language.relations.items())
        self.control_var = z3.FreshInt("cv_atom", env.context)
        # we need at least 2 arguments since we have equality
        self.arguments = tuple(TermVariable(env, language, term_depth, num_vars) for _ in range(max(2, language.get_max_relation_arity())))

    def get_well_formedness_constraint(self) -> BoolRef:
        constraint = \
            z3.If(
                z3.Or(self.control_var == 0, self.control_var == 1),
                z3.And(*(argument.get_is_null_constraint() for argument in self.arguments)),
            z3.If(
                # constraints for equality well-formedness
                self.control_var == 2,
                z3.And(
                    z3.And(*(argument.get_well_formedness_constraint() for argument in self.arguments[:2])),
                    z3.And(*(argument.get_is_null_constraint() for argument in self.arguments[2:])),
                ),
                False,
            ))

        for i, (_, arity) in enumerate(self.relations, 3):
            constraint = z3.If(
                self.control_var == i,
                z3.And(
                    z3.And(*(argument.get_well_formedness_constraint() for argument in self.arguments[:arity])),
                    z3.And(*(argument.get_is_null_constraint() for argument in self.arguments[arity:])),
                ),
                constraint,
            )

        return constraint
        
    def eval(self, structure: Structure, assignment: Tuple[AstRef, ...]) -> BoolRef:
        """
        Evaluate an formula to a boolean value in z3
        """

        result = \
            z3.If(
                self.control_var == 0,
                False,
            z3.If(
                self.control_var == 1,
                True,
            z3.If(
                self.control_var == 2,
                self.arguments[0].eval(structure, assignment) == self.arguments[1].eval(structure, assignment),
                False,
            )))

        for i, (symbol, arity) in enumerate(self.relations, 3):
            arguments = tuple(argument.eval(structure, assignment) for argument in self.arguments[:arity])
            result = z3.If(
                self.control_var == i,
                structure.eval_relation(symbol, arguments),
                result,
            )

        return result

    def unparse_z3_model(self, model: ModelRef) -> str:
        """
        Unparse a formula from the given model
        """

        control_val = model[self.control_var].as_long()

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
