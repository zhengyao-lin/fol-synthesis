from typing import Any

from synthesis import *
from synthesis import modal


def exhaust_variable(var: Template[Any]) -> None:
    with smt.Solver(name="z3") as solver:
        solver.add_assertion(var.get_constraint())

        while solver.solve():
            val = var.get_from_smt_model(solver.get_model())
            print(val)
            solver.add_assertion(smt.Not(var.equals(val)))

exhaust_variable(modal.ModalFormulaTemplate(
    (modal.Atom("p"),),
    1,
))
