from typing import Any, Callable, Tuple

from pysmt.shortcuts import FreshSymbol, TRUE, FALSE, And, Or, Not, Implies, Iff, Ite, Equals, BV, get_model, Solver, ForAll, Exists, Int, GT, GE, LT, LE # type: ignore
from pysmt.typing import BOOL, INT, BVType, FunctionType # type: ignore

from pysmt.shortcuts import Function as Apply

SMTTerm = Any
SMTSolver = Any
SMTModel = Any
SMTSort = Any
SMTVariable = Any
SMTFunction = Callable[..., SMTTerm]


def FreshFunction(input_sorts: Tuple[SMTSort, ...], output_sort: SMTSort) -> SMTFunction:
    symbol = FreshSymbol(FunctionType(output_sort, input_sorts))
    return lambda *args: Apply(symbol, args)
