from typing import Any, Callable, Tuple, Generator, Optional
from contextlib import contextmanager

import z3 # type: ignore


SMTTerm = Any
SMTSort = Any
SMTVariable = Any
SMTFunction = Callable[..., SMTTerm]
SMTScript = Any


BOOL = z3.BoolSort()
INT = z3.IntSort()

TRUE = lambda: z3.BoolVal(True)
FALSE = lambda: z3.BoolVal(False)
Bool = z3.BoolVal
Int = z3.IntVal

And = z3.And
Or = z3.Or
Not = z3.Not
Implies = z3.Implies
Iff = lambda a, b: a == b
Ite = z3.If

LE = lambda a, b: a <= b
Equals = lambda a, b: a == b


class IntNumRefWrapper:
    def __init__(self, val: z3.IntNumRef):
        self.val = val

    def constant_value(self) -> int:
        return self.val.as_long() # type: ignore


class SMTModel:
    def __init__(self, model: z3.Model):
        self.model = model

    def __getitem__(self, var: Any) -> Any:
        interp = self.model[var]
        assert interp is not None, f"{var} not found in model {self.model}"
        if isinstance(interp, z3.IntNumRef):
            return IntNumRefWrapper(interp)
        return interp


class SMTSolver:
    def __init__(self, solver: z3.Solver):
        self.solver = solver

    def add_assertion(self, term: SMTTerm) -> None:
        self.solver.add(term)
    
    def solve(self) -> bool:
        result = self.solver.check()
        assert result != z3.unknown, "Z3 returned unknown"
        return result == z3.sat # type: ignore

    def get_model(self) -> SMTModel:
        return SMTModel(self.solver.model())


@contextmanager
def Solver(logic: Optional[str] = None, **kwargs: Any) -> Generator[SMTSolver, None, None]:
    solver = z3.Solver()
    if logic is not None:
        solver.set("logic", logic)
    yield SMTSolver(solver)


def FreshSymbol(sort: SMTSort) -> SMTVariable:
    return z3.FreshConst(sort)


@contextmanager
def push_solver(solver: SMTSolver) -> Generator[None, None, None]:
    try:
        solver.solver.push()
        yield
    finally:
        solver.solver.pop()


_fresh_sort_index = 0

def FreshSort() -> SMTSort:
    global _fresh_sort_index
    sort = z3.DeclareSort(f"A{_fresh_sort_index}")
    _fresh_sort_index += 1
    return sort


def FreshFunction(input_sorts: Tuple[SMTSort, ...], output_sort: SMTSort) -> SMTFunction:
    function = z3.FreshFunction(*input_sorts, output_sort)
    return lambda *args: function(*args)


class SMTLIB:
    @staticmethod
    def parse_sort(src: str) -> SMTSort:
        return z3.parse_smt2_string(f"(declare-const x {src}) (assert (= x x))")[0].children()[0].sort()

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
                smt_sort = arg.sort()

                if smt_sort.kind() == z3.Z3_UNINTERPRETED_SORT:
                    custom_sorts.add(smt_sort)

                var = f"x{i}"
                substitution[z3.Const(var, smt_sort)] = arg
                declarations.append(f"(declare-const {var} {smt_sort.sexpr()})")
                term_str = term_str.replace(f"#{i}", var)

            # declare uninterpreted sorts
            declarations = [ f"(declare-sort {str(sort)})" for sort in custom_sorts ] + declarations

            try:
                script_src = " ".join(declarations) + f" (assert (= {term_str} {term_str}))"
                term = z3.parse_smt2_string(script_src)[0].children()[0]
            except Exception as e:
                raise Exception(f"unable to parse {script_src}: {e}")

            return z3.substitute(term, *tuple(substitution.items()))

        return function
