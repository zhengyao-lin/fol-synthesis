from typing import Any

from fol import *


sort_a = Sort("A")
sort_b = Sort("B")

language = Language(
    (sort_a, sort_b),
    (), # (FunctionSymbol((sort_a, sort_b), sort_a, "f"), FunctionSymbol((sort_a,), sort_b, "g"), FunctionSymbol((), sort_b, "nil")),
    # (RelationSymbol((sort_a,), "R"),),
    (),
    # (RelationSymbol((), "B"),)
)

free_vars = (Variable("x", sort_a), Variable("y", sort_b))

def exhaust_variable(var: Template[Any]) -> None:
    structure = UninterpretedModelVariable(language, smt.INT)

    with smt.Solver(name="z3") as solver:
        solver.add_assertion(var.get_constraint())

        while solver.solve():
            val = var.get_from_smt_model(solver.get_model())
            print(val)
            solver.add_assertion(smt.Not(var.equals(val)))

# term_var = TermTemplate(language, free_vars, 2)
# atomic_formula_var = AtomicFormulaTemplate(language, free_vars, 0)
exhaust_variable(QuantifierFreeFormulaTemplate(language, (), 0, 1)) # should generate 42 items
