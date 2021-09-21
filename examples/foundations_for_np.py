from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer

# Snythesizing examples in the Foundations for Natural Proof paper

# Four theories
# - Theory of linked lists (list, lseg)
# - Theory of doubly linked lists (dlist, dlseg)
# - Theory of sorted lists (slist and slseg)
# - Theory of binary search trees (btree, bst)

theory_map = Parser.parse_theories(r"""
theory HEAP
    sort Pointer
    constant nil: Pointer
end

theory LIST-BASE extending HEAP
    function next: Pointer -> Pointer
    function prev: Pointer -> Pointer
end

theory LIST extending LIST-BASE
    relation list: Pointer
    relation lseg: Pointer Pointer

    relation in_lsegf: Pointer Pointer Pointer // in the forward list segment (prev)
    fixpoint in_lsegf(x, y, z) = y != z /\ (x = y \/ in_lsegf(x, next(y), z))

    fixpoint list(x) = x = nil() \/ (list(next(x)) /\ not in_lsegf(x, next(x), nil()))
    fixpoint lseg(x, y) = x = y \/ (lseg(next(x), y) /\ not in_lsegf(x, next(x), y))
end

theory DLIST extending LIST
    relation dlist: Pointer
    relation dlseg: Pointer Pointer

    relation in_lsegb: Pointer Pointer Pointer // in the backward list segment (prev)
    fixpoint in_lsegb(x, y, z) = y != z /\ (x = z \/ in_lsegb(x, y, prev(z)))

    fixpoint dlist(x) =
        x = nil() \/ next(x) = nil() \/
        (
            prev(next(x)) = x /\
            dlist(next(x)) /\
            not in_lsegf(x, next(x), nil()) /\
            not in_lsegb(x, nil(), prev(x))
        )

    fixpoint dlseg(x, y) =
        x = y \/
        (
            prev(next(x)) = x /\
            dlseg(next(x), y) /\
            not in_lsegf(x, next(x), y) /\
            not in_lsegb(x, nil(), prev(x))
        )
end

theory REV extending DLIST
    relation rev: Pointer Pointer
    fixpoint rev(x, y) =
        (x = nil() /\ y = nil()) \/
        (x = y /\ rev(next(x), prev(y)))
end
""")

theory = theory_map["LIST"]

sort_pointer = theory.language.get_sort("Pointer")

language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil",),
    ("list", "lseg"),
)

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
