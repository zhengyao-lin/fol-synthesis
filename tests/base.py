from typing import TypeVar, Set

import unittest

from fol import *


S = TypeVar("S")


class TestCase(unittest.TestCase):
    def enumerate(self, template: Template[S], solver_name: str = "z3") -> Set[S]:
        """
        Enumerate all values in a finite template
        """

        values: Set[S] = set()

        with smt.Solver(name=solver_name) as solver:
            solver.add_assertion(template.get_constraint())

            while solver.solve():
                value = template.get_from_smt_model(solver.get_model())
                solver.add_assertion(smt.Not(template.equals(value)))
                values.add(value)

        return values
