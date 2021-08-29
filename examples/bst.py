from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


theory = Parser.parse_theory(r"""
theory BST
    sort Pointer
    sort Int [smt("Int")]

    constant c: Int

    constant nil: Pointer
    function left: Pointer -> Pointer
    function right: Pointer -> Pointer
    function key: Pointer -> Int
    
    relation btree: Pointer
    relation bst: Pointer
    relation leftmost: Pointer Int
    relation in_btree: Pointer Pointer

    relation le_int: Int Int [smt("(<= #1 #2)")]
    relation eq_int: Int Int [smt("(= #1 #2)")]

    relation eq_pointer: Pointer Pointer [smt("(= #1 #2)")]
    relation ne_pointer: Pointer Pointer [smt("(not (= #1 #2))")]

    fixpoint in_btree(x, y) =
        not eq_pointer(y, nil()) /\
        (eq_pointer(x, y) \/ in_btree(x, left(y)) \/ in_btree(x, right(y)))
    
    fixpoint btree(x) =
        eq_pointer(x, nil()) \/
        (eq_pointer(left(x), nil()) /\ eq_pointer(right(x), nil())) \/
        (btree(left(x)) /\ btree(right(x)) /\ not in_btree(x, left(x)) /\ not in_btree(x, right(x)))

    fixpoint bst(x) =
        eq_pointer(x, nil()) \/
        (eq_pointer(left(x), nil()) /\ eq_pointer(right(x), nil())) \/
        (
            le_int(key(left(x)), key(x)) /\
            le_int(key(x), key(right(x))) /\
            bst(left(x)) /\
            bst(right(x)) /\
            not in_btree(x, left(x)) /\
            not in_btree(x, right(x))
        )

    fixpoint leftmost(x, v) =
        not eq_pointer(x, nil()) /\
        ((eq_pointer(left(x), nil()) /\ eq_int(key(x), v)) \/ leftmost(left(x), v))
end
""")

language = theory.language.get_sublanguage(
    ("Pointer", "Int"),
    ("nil", "left", "right", "key", "c"),
    ("btree", "bst", "leftmost", "le_int")
)

sort_pointer = language.get_sort("Pointer")

x = Variable("x", sort_pointer)

trivial_model = FOProvableStructureTemplate(theory, unfold_depth=2)
goal_model = FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 5 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        # first synthesize R(...) -> S(...)
        # then synthesize R1(...) /\ R2(...) -> S(...)
        Implication(
            AtomicFormulaTemplate(language, (x,), 0),
            AtomicFormulaTemplate(language, (x,), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x,), 0),
                AtomicFormulaTemplate(language, (x,), 0),
            ),
            AtomicFormulaTemplate(language, (x,), 1),
        ),
    ),
    trivial_model,
    goal_model,
): ...
