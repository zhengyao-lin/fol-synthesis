from fol import *


theory = Parser.parse_theory(r"""
theory DLIST
    sort Pointer
    sort Int [smt("Int")]

    constant c: Int

    constant nil: Pointer
    function prev: Pointer -> Pointer
    function next: Pointer -> Pointer

    function key: Pointer -> Int
    relation in_keys: Int Pointer

    relation list: Pointer
    // relation lsegf: Pointer Pointer
    relation dlist: Pointer
    relation dlseg: Pointer Pointer

    relation rev: Pointer Pointer

    relation in_lsegf: Pointer Pointer Pointer // in the forward list segment (next)
    relation in_lsegb: Pointer Pointer Pointer // in the backend list segment (prev)

    relation in_listf: Pointer Pointer
    relation in_listb: Pointer Pointer

    relation eq_pointer: Pointer Pointer [smt("(= #1 #2)")]
    relation eq_int: Int Int [smt("(= #1 #2)")]

    fixpoint in_listf(x, y) = not eq_pointer(y, nil()) /\ (eq_pointer(x, y) \/ in_listf(x, next(y)))
    fixpoint in_listb(x, y) = not eq_pointer(y, nil()) /\ (eq_pointer(x, y) \/ in_listb(x, prev(y)))

    fixpoint in_lsegf(x, y, z) = not eq_pointer(y, z) /\ (eq_pointer(x, y) \/ in_lsegf(x, next(y), z))
    fixpoint in_lsegb(x, y, z) = not eq_pointer(y, z) /\ (eq_pointer(x, z) \/ in_lsegb(x, y, prev(z)))

    fixpoint list(x) = eq_pointer(x, nil()) \/ (list(next(x)) /\ not in_listf(x, next(x)))
    // fixpoint lsegf(x, y) = eq_pointer(x, y) \/ (lsegf(next(x), y) /\ not in_lsegf(x, next(x), y))

    fixpoint dlist(x) =
        eq_pointer(x, nil()) \/
        eq_pointer(next(x), nil()) \/
        (
            eq_pointer(prev(next(x)), x) /\
            dlist(next(x)) /\
            not in_listf(x, next(x)) /\
            not in_listb(x, prev(x))
        )

    fixpoint dlseg(x, y) =
        eq_pointer(x, y) \/
        (
            eq_pointer(prev(next(x)), x) /\
            dlseg(next(x), y) /\
            not in_lsegf(x, next(x), y) /\
            not in_lsegb(x, nil(), prev(x))
        )

    fixpoint rev(x, y) =
        (eq_pointer(x, nil()) /\ eq_pointer(y, nil())) \/
        (eq_pointer(x, y) /\ rev(next(x), prev(y)))
end
""")

sort_pointer = theory.language.get_sort("Pointer")
assert sort_pointer is not None

sort_int = theory.language.get_sort("Int")
assert sort_int is not None

language = theory.language.get_sublanguage(
    ("Pointer", "Int"),
    ("nil", "next", "prev"),
    ("list", "dlist", "dlseg"),
)

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)

trivial_model = FOProvableModelVariable(theory, unfold_depth=2)
goal_model = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 4 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        Implication(
            AtomicFormulaTemplate(language, (x, y), 0),
            AtomicFormulaTemplate(language, (x, y), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y), 0),
                AtomicFormulaTemplate(language, (x, y), 0),
            ),
            AtomicFormulaTemplate(language, (x, y), 0),
        ),
    ),
    trivial_model,
    goal_model,
): ...

