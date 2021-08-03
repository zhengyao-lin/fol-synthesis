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

def exhaust_variable(var: Template[Any]) -> None:
    with smt.Solver(name="z3") as solver:
        solver.add_assertion(var.get_constraint())

        while solver.solve():
            val = var.get_from_smt_model(solver.get_model())
            print(val)
            solver.add_assertion(smt.Not(var.equals(val)))

f = FunctionSymbol((sort_a,), sort_a, "f")
A = RelationSymbol((), "A")
B = RelationSymbol((), "B")
C = RelationSymbol((sort_a,), "C")

language1 = Language(
    (sort_a,),
    (f,),
    (A, C),
)

language2 = Language(
    (sort_a,),
    (),
    (B,)
)

x = Variable("x", sort_a)
y = Variable("y", sort_a)

# exhaust_variable(UnionFormulaTemplate(
#     QuantifierFreeFormulaTemplate(language1, (), 0, 1),
#     QuantifierFreeFormulaTemplate(language2, (), 0, 1),
# )) # should generate 12 items

exhaust_variable(QuantifierFreeFormulaTemplate(language1, (x,), 0, 1).substitute(
    {
        x: Application(f, (x,))
    }
).substitute(
    {
        x: Application(f, (x,))
    }
))
