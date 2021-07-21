from typing import Any

from synthesis.smt import get_model, Solver, Not
from synthesis.fol.ast import *
from synthesis.synthesis import *


sort_a = UninterpretedSort("A")
sort_b = UninterpretedSort("B")

language = Language(
    (sort_a, sort_b),
    (FunctionSymbol((sort_a, sort_b), sort_a, "f"), FunctionSymbol((sort_a,), sort_b, "g")),
    (RelationSymbol((sort_a, sort_b), "R"),),
)

free_vars = (Variable("x", sort_a), Variable("y", sort_b))

def exhaust_variable(var: VariableWithConstraint[Any]) -> None:
    with Solver(name="z3") as solver:
        var.add_to_solver(solver)

        while solver.solve():
            val = var.get_from_model(solver.get_model())
            print(val)
            solver.add_assertion(Not(var.equals(val)))


# term_var = TermVariable(language, free_vars, 2)
atomic_formula_var = AtomicFormulaVariable(language, free_vars, 1)
exhaust_variable(atomic_formula_var)
