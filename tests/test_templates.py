
"""
TODO:
1. basic enumeration of term and formula tempaltes [-]
2. enumeration of union template
3. equality for basic term and formlua templates
4. equality for union template
5. free variables of term and formula templates
6. free variables of union template
7. substitution of templates
8. substitution of templates then free variable
9. substitution of templates then equality
10. double substitutions of templates
11. substitution with templates (i.e. substitute variables with templates)
"""

from synthesis import *

from .base import TestCase


class TestFormulaTemplates(TestCase):
    def test_template_substitution(self) -> None:
        sort_a = Sort("A")

        f = FunctionSymbol((sort_a, sort_a), sort_a, "f")
        c = FunctionSymbol((), sort_a, "c")

        R = RelationSymbol((sort_a,), "R")

        x = Variable("x", sort_a)
        y = Variable("y", sort_a)
        z = Variable("z", sort_a)

        language = Language(
            (sort_a,),
            (f, c),
            (R,),
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (), 1)),
            {
                Application(c, ()),
                Application(f, (Application(c, ()), Application(c, ()))),
            },
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (), 2)),
            {
                Application(c, ()),
                Application(f, (Application(c, ()), Application(c, ()))),
                Application(f, (Application(f, (Application(c, ()), Application(c, ()))), Application(c, ()))),
                Application(f, (Application(c, ()), Application(f, (Application(c, ()), Application(c, ()))))),
                Application(f, (Application(f, (Application(c, ()), Application(c, ()))), Application(f, (Application(c, ()), Application(c, ()))))),
            },
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (x,), 1).substitute({ x: Application(c, ()) })),
            self.enumerate(TermTemplate(language, (), 1)),
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (x,), 1).substitute({ x: TermTemplate(language, (), 1) })),
            self.enumerate(TermTemplate(language, (), 2)),
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (x,), 1)
                .substitute({ x: TermTemplate(language, (x,), 1) })
                .substitute({ x: Application(c, ()) })),
            self.enumerate(TermTemplate(language, (), 2)),
        )

        language2 = Language(
            (sort_a,),
            (),
            (R,)
        )

        self.assertEqual(
            self.enumerate(QuantifierFreeFormulaTemplate(language2, (x,), 0, 1)
                .substitute({ x: TermTemplate(language, (x,), 1) })
                .substitute({ x: Application(c, ()) })),
            self.enumerate(QuantifierFreeFormulaTemplate(language, (x, y), 1, 1)
                .substitute({ x: y, y: Application(c, ()) })
                .substitute({ y: z })
                .substitute({ z: TermTemplate(language, (), 0) })),
        )

    def test_union_templates_for_singletons(self) -> None:
        sort_a = Sort("A")

        x = Variable("x", sort_a)
        y = Variable("y", sort_a)
        z = Variable("z", sort_a)

        self.assertEqual(self.enumerate(UnionTermTemplate(x, y, z)), { x, y, z })
        self.assertEqual(self.enumerate(UnionTermTemplate(x, x, y)), { x, y })
        self.assertEqual(UnionTermTemplate(x, y).get_free_variables(), { x, y })

        # for a template denoting multiple formulas
        # substitution is applied pointwise
        self.assertEqual(self.enumerate(UnionTermTemplate(x, y, z).substitute({ x: y, y: z })), { y, z })

        self.assertEqual(UnionTermTemplate(x, y, z).substitute({ x: y, y: z }).get_free_variables(), { y, z })
        self.assertEqual(UnionTermTemplate(x, y, z).substitute({ x: z, y: z }).get_free_variables(), { z })

    def test_union_templates_for_templates(self) -> None:
        sort_a = Sort("A")

        f = FunctionSymbol((sort_a, sort_a), sort_a, "f")
        c = FunctionSymbol((), sort_a, "c")

        R = RelationSymbol((sort_a,), "R")

        x = Variable("x", sort_a)

        language = Language(
            (sort_a,),
            (f, c),
            (),
        )

        self.assertEqual(
            self.enumerate(UnionFormulaTemplate(
                RelationApplication(R, (TermTemplate(language, (x,), 1),)),
                RelationApplication(R, (TermTemplate(language, (x,), 2),)),
            )),
            self.enumerate(RelationApplication(R, (TermTemplate(language, (x,), 2),))),
        )

    def test_atomic_formula_enumeration(self) -> None:
        sort_a = Sort("A")

        f = FunctionSymbol((sort_a, sort_a), sort_a, "f")

        R = RelationSymbol((sort_a,), "R")
        P = RelationSymbol((), "P")
        Q = RelationSymbol((), "Q")

        x = Variable("x", sort_a)

        language = Language(
            (sort_a,),
            (f,),
            (R, P, Q),
        )

        self.assertEqual(
            self.enumerate(AtomicFormulaTemplate(language, (x,), 0)),
            {
                RelationApplication(R, (x,)),
                RelationApplication(P, ()),
                RelationApplication(Q, ()),
            },
        )

        self.assertEqual(
            self.enumerate(AtomicFormulaTemplate(language, (x,), 1)),
            {
                RelationApplication(R, (x,)),
                RelationApplication(R, (Application(f, (x, x)),)),
                RelationApplication(P, ()),
                RelationApplication(Q, ()),
            },
        )

    def test_quantifier_free_formula_enumeration(self) -> None:
        sort_a = Sort("A")

        f = FunctionSymbol((sort_a, sort_a), sort_a, "f")

        R = RelationSymbol((sort_a,), "R")
        P = RelationSymbol((), "P")

        x = Variable("x", sort_a)

        language = Language(
            (sort_a,),
            (f,),
            (R, P),
        )

        self.assertEqual(
            self.enumerate(QuantifierFreeFormulaTemplate(language, (), 0, 1)),
            {
                RelationApplication(P, ()),
                Negation(RelationApplication(P, ())),
                Conjunction(RelationApplication(P, ()), RelationApplication(P, ())),
                Disjunction(RelationApplication(P, ()), RelationApplication(P, ())),
                Implication(RelationApplication(P, ()), RelationApplication(P, ())),
                Equivalence(RelationApplication(P, ()), RelationApplication(P, ())),
            },
        )

        self.assertEqual(
            self.enumerate(QuantifierFreeFormulaTemplate(language, (x,), 0, 1)),
            {
                RelationApplication(R, (x,)),
                RelationApplication(P, ()),
                Negation(RelationApplication(R, (x,))),
                Negation(RelationApplication(P, ())),
                Conjunction(RelationApplication(P, ()), RelationApplication(P, ())),
                Disjunction(RelationApplication(P, ()), RelationApplication(P, ())),
                Implication(RelationApplication(P, ()), RelationApplication(P, ())),
                Equivalence(RelationApplication(P, ()), RelationApplication(P, ())),
                Conjunction(RelationApplication(R, (x,)), RelationApplication(R, (x,))),
                Disjunction(RelationApplication(R, (x,)), RelationApplication(R, (x,))),
                Implication(RelationApplication(R, (x,)), RelationApplication(R, (x,))),
                Equivalence(RelationApplication(R, (x,)), RelationApplication(R, (x,))),
                Conjunction(RelationApplication(R, (x,)), RelationApplication(P, ())),
                Disjunction(RelationApplication(R, (x,)), RelationApplication(P, ())),
                Implication(RelationApplication(R, (x,)), RelationApplication(P, ())),
                Equivalence(RelationApplication(R, (x,)), RelationApplication(P, ())),
                Conjunction(RelationApplication(P, ()), RelationApplication(R, (x,))),
                Disjunction(RelationApplication(P, ()), RelationApplication(R, (x,))),
                Implication(RelationApplication(P, ()), RelationApplication(R, (x,))),
                Equivalence(RelationApplication(P, ()), RelationApplication(R, (x,))),
            },
        )

    def test_term_enumeration(self) -> None:
        sort_a = Sort("A")

        f = FunctionSymbol((sort_a, sort_a), sort_a, "f")
        c = FunctionSymbol((), sort_a, "c")

        x = Variable("x", sort_a)

        language = Language(
            (sort_a,),
            (f, c),
            (),
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (), 1)),
            {
                Application(c, ()),
                Application(f, (Application(c, ()), Application(c, ()))),
            }
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (), 2)),
            {
                Application(c, ()),
                Application(f, (Application(c, ()), Application(c, ()))),
                Application(f, (
                    Application(f, (Application(c, ()), Application(c, ()))),
                    Application(c, ()),
                )),
                Application(f, (
                    Application(c, ()),
                    Application(f, (Application(c, ()), Application(c, ()))),
                )),
                Application(f, (
                    Application(f, (Application(c, ()), Application(c, ()))),
                    Application(f, (Application(c, ()), Application(c, ()))),
                )),
            }
        )

        self.assertEqual(
            self.enumerate(TermTemplate(language, (x,), 1)),
            {
                x,
                Application(c, ()),
                Application(f, (Application(c, ()), Application(c, ()))),
                Application(f, (x, Application(c, ()))),
                Application(f, (Application(c, ()), x)),
                Application(f, (x, x)),
            }
        )

    def test_term_enumeration_sorting(self) -> None:
        sort_a = Sort("A")
        sort_b = Sort("B")
        sort_c = Sort("C")

        f = FunctionSymbol((sort_a, sort_b), sort_c, "f")
        g = FunctionSymbol((sort_a,), sort_b, "g")

        x = Variable("x", sort_a)
        y = Variable("y", sort_b)
        z = Variable("z", sort_c)

        language = Language(
            (sort_a,),
            (f, g),
            (),
        )

        self.assertEqual(self.enumerate(TermTemplate(language, (x, y, z), 1, sort_a)), { x })
        self.assertEqual(self.enumerate(TermTemplate(language, (x, y, z), 1, sort_c)), {
            z,
            Application(f, (x, y)),
        })
        self.assertEqual(self.enumerate(TermTemplate(language, (x, y, z), 2, sort_c)), {
            z,
            Application(f, (x, y)),
            Application(f, (x, Application(g, (x,)))),
        })
