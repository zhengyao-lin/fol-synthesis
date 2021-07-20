
from pysmt.shortcuts import get_model, Solver, Not

from synthesis.fol.ast import *
from synthesis.synthesis import *


sort_a = UninterpretedSort("A")
sort_b = UninterpretedSort("B")

language = Language(
    (sort_a, sort_b),
    (FunctionSymbol((sort_a, sort_b), sort_a, "f"), FunctionSymbol((sort_a,), sort_b, "g")),
    (),
)

free_vars = (Variable("x", sort_a), Variable("y", sort_b))

term_var = TermVariable(language, free_vars, 2)

with Solver(name="z3") as solver:
    term_var.add_to_solver(solver)

    while solver.solve():
        term = term_var.get_from_model(solver.get_model())
        print(term)
        solver.add_assertion(Not(term_var.equals(term)))
