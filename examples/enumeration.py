from typing import Any

from synthesis.smt import get_model, Solver, Not
from synthesis.fol import *
from synthesis.synthesis import *


sort_a = Sort("A")
sort_b = Sort("B")

language = Language(
    (sort_a, sort_b),
    (FunctionSymbol((sort_a, sort_b), sort_a, "f"), FunctionSymbol((sort_a,), sort_b, "g"), FunctionSymbol((), sort_b, "nil")),
    (RelationSymbol((sort_a, sort_b), "R"),),
)

free_vars = (Variable("x", sort_a), Variable("y", sort_b))

def exhaust_variable(var: Template[Any]) -> None:
    with Solver(name="z3") as solver:
        solver.add_assertion(var.get_constraint())

        while solver.solve():
            val = var.get_from_smt_model(solver.get_model())
            print(val)
            solver.add_assertion(Not(var.equals(val)))

# term_var = TermVariable(language, free_vars, 2)
atomic_formula_var = AtomicFormulaVariable(language, free_vars, 0)
exhaust_variable(atomic_formula_var)
