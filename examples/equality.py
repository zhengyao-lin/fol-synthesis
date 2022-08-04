from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


eq_theory = Parser.parse_theory(r"""
theory EQUALITY
    sort A
    relation eq: A A [smt("(= #1 #2)")]
    function f: A -> A
end
""")

empty_theory = Parser.parse_theory(r"""
theory EQUALITY
    sort A
    relation eq: A A
    function f: A -> A
end
""")

language = eq_theory.language.get_sublanguage(
    ("A"),
    ("f",),
    ("eq",),
)

sort_a = language.get_sort("A")

x = Variable("x", sort_a)
y = Variable("y", sort_a)
z = Variable("z", sort_a)

trivial_model = FiniteFOModelTemplate(empty_theory, size_bounds={ sort_a: 5 })
goal_model = FiniteFOModelTemplate(eq_theory, size_bounds={ sort_a: 5 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        AtomicFormulaTemplate(language, (x, y), 1),
        Implication(
            AtomicFormulaTemplate(language, (x, y), 2),
            AtomicFormulaTemplate(language, (x, y), 2),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y, z), 2),
                AtomicFormulaTemplate(language, (x, y, z), 2),
            ),
            AtomicFormulaTemplate(language, (x, y, z), 2),
        ),
    ),
    trivial_model,
    goal_model,
): ...

