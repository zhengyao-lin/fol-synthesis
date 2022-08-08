from typing import Any

from synthesis import *
from synthesis import modal


def exhaust_variable(var: Template[Any]) -> List[Formula]:
    everything = []

    with smt.Solver(name="z3") as solver:
        solver.add_assertion(var.get_constraint())

        while solver.solve():
            val = var.get_from_smt_model(solver.get_model())
            everything.append(val)
            solver.add_assertion(smt.Not(var.equals(val)))

    return everything


template = modal.ModalFormulaTemplate(
    (modal.Atom("p"),),
    (
        # modal.Connective(lambda f: modal.Diamond(modal.Negation(f)), 1),
        # modal.Connective(modal.Box, 1),

        modal.Connective(modal.Falsum, 0),

        modal.Connective(modal.Implication, 2),
        modal.Connective(modal.Disjunction, 2),
        modal.Connective(modal.Conjunction, 2),
        modal.Connective(modal.Negation, 1),

        modal.Connective(modal.Box, 1),
        # modal.Connective(modal.BoxPast, 1),
        modal.Connective(modal.Diamond, 1),
        # modal.Connective(modal.DiamondPast, 1),
    ),
    2,
)

print(len(list(template.enumerate())))

# enumerated_1 = exhaust_variable(template)
# enumerated_2 = list(template.enumerate())

# set_1 = set(enumerated_1)
# set_2 = set(enumerated_2)

# assert len(enumerated_1) == len(set_1), "duplicate"
# assert len(enumerated_2) == len(set_2), "duplicate"
# assert set_1 == set_2, "different enumeration results"
