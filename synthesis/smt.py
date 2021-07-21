
from typing import Any

from pysmt.shortcuts import FreshSymbol, TRUE, FALSE, And, Or, Not, Implies, Iff, Ite, Equals, BV, get_model, Solver, ForAll, Exists, Int # type: ignore
from pysmt.typing import BOOL, INT, BVType, FunctionType # type: ignore

from pysmt.shortcuts import Function as Apply

SMTTerm = Any
SMTSolver = Any
SMTModel = Any
SMTSort = Any
SMTVariable = Any
