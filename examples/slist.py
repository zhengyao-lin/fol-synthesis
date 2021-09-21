from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


theory = Parser.parse_theory(r"""
theory SLIST
    sort Pointer
    sort Int [smt("Int")]

    constant nil: Pointer
    function next: Pointer -> Pointer

    function key: Pointer -> Int

    relation list: Pointer
    relation slist: Pointer
    relation lseg: Pointer Pointer
    relation slseg: Pointer Pointer
    relation in_lseg: Pointer Pointer Pointer

    relation eq: Pointer Pointer [smt("(= #1 #2)")]
    relation le_int: Int Int [smt("(<= #1 #2)")]

    fixpoint in_lseg(x, y, z) = not eq(y, z) /\ (eq(x, y) \/ in_lseg(x, next(y), z))
    fixpoint list(x) = eq(x, nil()) \/ (list(next(x)) /\ not in_lseg(x, next(x), nil()))
    fixpoint lseg(x, y) = eq(x, y) \/ (lseg(next(x), y) /\ not in_lseg(x, next(x), y))

    fixpoint slist(x) = eq(x, nil()) \/ eq(next(x), nil()) \/ (le_int(key(x), key(next(x))) /\ slist(next(x)) /\ not in_lseg(x, next(x), nil()))

    fixpoint slseg(x, y) = eq(x, y) \/ (le_int(key(x), key(next(x))) /\ slseg(next(x), y) /\ not in_lseg(x, next(x), y))
end
""")

language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "next"),
    ("list", "lseg", "slist", "slseg"),
)

sort_pointer = language.get_sort("Pointer")

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

# free variables are universally quantified
template = Implication(
    Conjunction(
        AtomicFormulaTemplate(language, (x, y, z), 0),
        AtomicFormulaTemplate(language, (x, y, z), 0),
    ),
    AtomicFormulaTemplate(language, (x, y, z), 0),
)

trivial_model = FOProvableStructureTemplate(theory, unfold_depth=2)
goal_model = FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
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
        ),
    ),
    trivial_model,
    goal_model,
): ...
