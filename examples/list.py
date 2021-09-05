from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


theory = Parser.parse_theory(r"""
theory LIST
    sort Pointer

    constant nil: Pointer
    function n: Pointer -> Pointer

    relation list: Pointer
    relation lseg: Pointer Pointer
    relation in_lseg: Pointer Pointer Pointer

    fixpoint in_lseg(x, y, z) = y != z /\ (x = y \/ in_lseg(x, n(y), z))
    fixpoint list(x) = x = nil() \/ (list(n(x)) /\ not in_lseg(x, n(x), nil()))
    fixpoint lseg(x, y) = x = y \/ (lseg(n(x), y) /\ not in_lseg(x, n(x), y))
end
""")

language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "n"),
    ("list", "lseg"),
)

sort_pointer = language.get_sort("Pointer")

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

trivial_model = FOProvableStructureTemplate(theory, unfold_depth=2)
goal_model = FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        # first synthesize R(...) -> S(...)
        # then synthesize R1(...) /\ R2(...) -> S(...)
        Implication(
            AtomicFormulaTemplate(language, (x, y, z), 0),
            AtomicFormulaTemplate(language, (x, y, z), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y, z), 0),
                AtomicFormulaTemplate(language, (x, y, z), 0),
            ),
            AtomicFormulaTemplate(language, (x, y, z), 0),
        )

        # QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 2),
    ),
    trivial_model,
    goal_model,
): ...
