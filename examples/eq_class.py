from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


eq_theory = Parser.parse_theory(r"""
theory EQ-CLASS
    sort Elem
    sort EClass
    function quotient: Elem -> EClass
    relation equivalent: Elem Elem
    axiom forall x: Elem, y: Elem. equivalent(x, y) <-> quotient(x) = quotient(y)
end
""")

language = eq_theory.language.get_sublanguage(
    ("Elem", "EClass"),
    (),
    ("equivalent",),
)

sort_elem = language.get_sort("Elem")
sort_eclass = language.get_sort("EClass")

x = Variable("x", sort_elem)
y = Variable("y", sort_elem)
z = Variable("z", sort_elem)

trivial_model = FiniteLFPModelTemplate(Theory.empty_theory(language), size_bounds={ sort_elem: 5, sort_eclass: 5 })
goal_model = FiniteLFPModelTemplate(eq_theory, size_bounds={ sort_elem: 5, sort_eclass: 5 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        # AtomicFormulaTemplate(language, (x, y), 1),
        # Implication(
        #     AtomicFormulaTemplate(language, (x, y), 2),
        #     AtomicFormulaTemplate(language, (x, y), 2),
        # ),
        # Implication(
        #     Conjunction(
        #         AtomicFormulaTemplate(language, (x, y, z), 2),
        #         AtomicFormulaTemplate(language, (x, y, z), 2),
        #     ),
        #     AtomicFormulaTemplate(language, (x, y, z), 2),
        # ),
        QuantifierFreeFormulaTemplate(language, (x, y), 0, 0),
        QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 1),
        QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 2),
        QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 3),
    ),
    trivial_model,
    goal_model,
): ...

