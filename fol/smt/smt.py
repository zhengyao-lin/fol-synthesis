from typing import Any, Callable, Tuple, Generator

from contextlib import contextmanager

from pysmt.shortcuts import \
    FreshSymbol, \
    TRUE, FALSE, And, Or, Not, Implies, Iff, ForAll, Exists, Ite, Equals, \
    GT, GE, LT, LE, \
    BV, Int, Bool, \
    get_model, Solver # type: ignore
from pysmt.typing import BOOL, INT, BVType, FunctionType, Type # type: ignore
from pysmt.smtlib.parser import SmtLibParser # type: ignore

from pysmt.shortcuts import Function as Apply

import io


SMTTerm = Any
SMTSolver = Any
SMTModel = Any
SMTSort = Any
SMTVariable = Any
SMTFunction = Callable[..., SMTTerm]
SMTScript = Any


def FreshFunction(input_sorts: Tuple[SMTSort, ...], output_sort: SMTSort) -> SMTFunction:
    symbol = FreshSymbol(FunctionType(output_sort, input_sorts))
    return lambda *args: Apply(symbol, args)


_fresh_sort_counter = 0


def FreshSort() -> SMTSort:
    global _fresh_sort_counter
    name = f"FreshSort{_fresh_sort_counter}"
    _fresh_sort_counter += 1
    return Type(name)


@contextmanager
def push_solver(solver: Solver) -> Generator[None, None, None]:
    try:
        solver.push()
        yield
    finally:
        solver.pop()


class SMTLIB:
    @staticmethod
    def parse_sort(src: str) -> SMTSort:
        variable = FreshSymbol().to_smtlib()
        return SmtLibParser().get_script(io.StringIO(f"(declare-const .{variable} {src}) (assert .{variable})")).get_last_formula().get_type()

    @staticmethod
    def parse_script(src: str) -> SMTScript:
        return SmtLibParser().get_script(io.StringIO(src))

    @staticmethod
    def parse_smt_function_from_template(src: str) -> SMTFunction:
        """
        Given a template such as (+ #1 #2)
        return a function that maps (x, y) |-> (+ x y)
        NOTE: indices start with 1
        """
        def function(*args: SMTTerm) -> SMTTerm:
            substitution = {}
            declarations = []
            term_str = src

            custom_sorts = set()

            for i, arg in enumerate(args, 1):
                smt_sort = arg.get_type()

                if smt_sort.is_custom_type():
                    custom_sorts.add(smt_sort)

                var = FreshSymbol(smt_sort)
                substitution[var] = arg
                declarations.append(f"(declare-fun {var.to_smtlib()} {var.get_type().as_smtlib()})")
                term_str = term_str.replace(f"#{i}", var.to_smtlib())

            # declare uninterpreted sorts
            declarations = [ f"(declare-sort {str(sort)} {sort.arity})" for sort in custom_sorts ] + declarations

            try:
                script_src = " ".join(declarations) + f" (assert {term_str})"
                script = SMTLIB.parse_script(script_src)
            except Exception as e:
                raise Exception(f"unable to parse {script_src}: {e}")

            return script.get_last_formula().substitute(substitution)

        return function
