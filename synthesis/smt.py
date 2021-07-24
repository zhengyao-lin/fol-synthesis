from typing import Any, Callable, Tuple

from pysmt.shortcuts import FreshSymbol, TRUE, FALSE, And, Or, Not, Implies, Iff, Ite, Equals, BV, get_model, Solver, ForAll, Exists, Int, GT, GE, LT, LE, Bool # type: ignore
from pysmt.typing import BOOL, INT, BVType, FunctionType # type: ignore
from pysmt.smtlib.parser import SmtLibParser

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

            for i, arg in enumerate(args, 1):
                var = FreshSymbol(arg.get_type())
                substitution[var] = arg
                declarations.append(f"(declare-fun {var.to_smtlib()} {var.get_type().as_smtlib()})")
                term_str = term_str.replace(f"#{i}", var.to_smtlib())

            try:
                script_src = " ".join(declarations) + f" (assert {term_str})"
                script = SMTLIB.parse_script(script_src)
            except Exception as e:
                raise Exception(f"unable to parse {script_src}: {e}")

            return script.get_last_formula().substitute(substitution)

        return function
