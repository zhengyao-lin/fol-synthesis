from fol import *

from .base import TestCase


class TestSyntax(TestCase):
    def test_basic_equality(self) -> None:
        sort_a = Sort("A")
        sort_b = Sort("B")
        sort_a_smt = Sort("A", smt_hook=smt.INT)

        self.assertEqual(sort_a, sort_a_smt)
        self.assertEqual(Variable("x", sort_a), Variable("x", sort_a))
        self.assertNotEqual(Variable("x", sort_a), Variable("y", sort_a))
        self.assertNotEqual(Variable("x", sort_a), Variable("x", sort_b))

        self.assertNotEqual(
            Conjunction(UniversalQuantification(Variable("x", sort_a), Falsum()), Falsum()),
            Conjunction(UniversalQuantification(Variable("x", sort_a), Verum()), Falsum()),
        )

    def test_basic_substitution(self) -> None:
        sort_a = Sort("A")
        
        f = FunctionSymbol((sort_a,), sort_a, "f")

        R = RelationSymbol((sort_a,), "R")

        x = Variable("x", sort_a)
        y = Variable("y", sort_a)

        self.assertEqual(x.substitute({ x: y }), y)
        self.assertEqual(
            Application(f, (x,)).substitute({ x: y }),
            Application(f, (y,)),
        )

        # shadowing
        self.assertEqual(
            UniversalQuantification(x, RelationApplication(R, (x,))).substitute({ x: y }),
            UniversalQuantification(x, RelationApplication(R, (x,))),
        )

        # substitution is not capture-free
        self.assertEqual(
            UniversalQuantification(x, RelationApplication(R, (y,))).substitute({ y: x }),
            UniversalQuantification(x, RelationApplication(R, (x,))),
        )

    def test_basic_free_variables(self) -> None:
        sort_a = Sort("A")
        
        g = FunctionSymbol((sort_a, sort_a), sort_a, "g")

        R = RelationSymbol((sort_a, sort_a), "R")

        x = Variable("x", sort_a)
        y = Variable("y", sort_a)

        self.assertEqual(x.get_free_variables(), { x })
        self.assertEqual(Application(g, (x, y)).get_free_variables(), { x, y })

        self.assertEqual(UniversalQuantification(x, RelationApplication(R, (x, x))).get_free_variables(), set())
        self.assertEqual(UniversalQuantification(x, RelationApplication(R, (x, y))).get_free_variables(), { y })

    def test_singleton_enumeration(self) -> None:
        sort_a = Sort("A")
        
        g = FunctionSymbol((sort_a, sort_a), sort_a, "g")

        R = RelationSymbol((sort_a, sort_a), "R")

        x = Variable("x", sort_a)
        y = Variable("y", sort_a)

        self.assertEqual(self.enumerate(x), { x })
        self.assertEqual(
            self.enumerate(UniversalQuantification(x, RelationApplication(R, (x, y)))),
            { UniversalQuantification(x, RelationApplication(R, (x, y))) },
        )
