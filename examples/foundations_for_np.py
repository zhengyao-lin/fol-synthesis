from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer

# Snythesizing examples in the "Foundations for Natural Proof" paper

theory_map = Parser.parse_theories(r"""
theory HEAP
    sort Pointer
    constant nil: Pointer
end

theory INT
    sort Int [smt("Int")]
    relation le_int: Int Int [smt("(<= #1 #2)")]
    constant zero: Int [smt("0")]
    constant one: Int [smt("1")]
    constant two: Int [smt("2")]    
    function minus: Int Int -> Int [smt("(- #1 #2)")]
end

theory LIST-BASE extending HEAP
    function next: Pointer -> Pointer
    function prev: Pointer -> Pointer
end

theory BTREE-BASE extending HEAP
    function left: Pointer -> Pointer
    function right: Pointer -> Pointer
end

theory LIST extending LIST-BASE
    relation list: Pointer
    relation lseg: Pointer Pointer

    relation in_lsegf: Pointer Pointer Pointer // in the forward list segment (prev)
    fixpoint in_lsegf(x, y, z) = y != z /\ (x = y \/ in_lsegf(x, next(y), z))

    fixpoint list(x) = x = nil() \/ (list(next(x)) /\ not in_lsegf(x, next(x), nil()))
    fixpoint lseg(x, y) = x = y \/ (lseg(next(x), y) /\ not in_lsegf(x, next(x), y))
end

theory LSEGR extending LIST
    // same as lseg but in defined in the reverse order
    relation lsegr: Pointer Pointer
    fixpoint lsegr(x, y) = x = y \/ (exists z: Pointer. next(z) = y /\ lsegr(x, z))
end

theory LIST1 extending LIST INT
    constant l: Int

    // list of length l
    relation list1: Pointer Int
    fixpoint list1(x, l) =
        (x = nil() /\ l = zero()) \/
        (
            x != nil() /\
            list1(next(x), minus(l, one())) /\
            not in_lsegf(x, next(x), nil())
        )
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

theory DLIST1 extending DLIST INT
    constant l: Int

    // list of length l
    relation dlist1: Pointer Int
    fixpoint dlist1(x, l) =
        (x = nil() /\ l = zero()) \/ (next(x) = nil() /\ l = one()) \/
        (
            prev(next(x)) = x /\
            dlist1(next(x), minus(l, one())) /\
            not in_lsegf(x, next(x), nil()) /\
            not in_lsegb(x, nil(), prev(x))
        )
end

theory REV extending DLIST
    relation rev: Pointer Pointer
    fixpoint rev(x, y) =
        (x = nil() /\ y = nil()) \/
        (x = y /\ rev(next(x), prev(y)))
end

theory SLIST extending LIST INT
    function key: Pointer -> Int

    relation slist: Pointer
    relation slseg: Pointer Pointer

    fixpoint slist(x) =
        x = nil() \/
        next(x) = nil() \/
        (
            le_int(key(x), key(next(x))) /\
            slist(next(x)) /\
            not in_lsegf(x, next(x), nil())
        )

    fixpoint slseg(x, y) =
        x = y \/
        (
            le_int(key(x), key(next(x))) /\
            slseg(next(x), y) /\
            not in_lsegf(x, next(x), y)
        )
end

theory SLIST1 extending SLIST INT
    constant l: Int

    // list of length l
    relation slist1: Pointer Int
    fixpoint slist1(x, l) =
        (x = nil() /\ l = zero()) \/
        (next(x) = nil() /\ l = one()) \/
        (
            le_int(key(x), key(next(x))) /\
            slist1(next(x), minus(l, one())) /\
            not in_lsegf(x, next(x), nil())
        )
end

theory BST extending BTREE-BASE INT
    constant c: Int
    function key: Pointer -> Int
    
    relation btree: Pointer
    relation bst: Pointer
    relation leftmost: Pointer Int
    relation in_btree: Pointer Pointer

    relation ne_pointer: Pointer Pointer [smt("(not (= #1 #2))")]

    fixpoint in_btree(x, y) =
        y != nil() /\ (x = y \/ in_btree(x, left(y)) \/ in_btree(x, right(y)))
    
    fixpoint btree(x) =
        x = nil() \/
        (left(x) = nil() /\ right(x) = nil()) \/
        (btree(left(x)) /\ btree(right(x)) /\ not in_btree(x, left(x)) /\ not in_btree(x, right(x)))

    fixpoint bst(x) =
        x = nil() \/
        (left(x) = nil() /\ right(x) = nil()) \/
        (
            le_int(key(left(x)), key(x)) /\
            le_int(key(x), key(right(x))) /\
            bst(left(x)) /\
            bst(right(x)) /\
            not in_btree(x, left(x)) /\
            not in_btree(x, right(x))
        )

    fixpoint leftmost(x, v) =
        x != nil() /\ ((left(x) = nil() /\ key(x) = v) \/ leftmost(left(x), v))
end
""")


def synthesize(theory: Theory, templates: Iterable[Formula], unfold_depth: int) -> None:
    sort_pointer = theory_map["HEAP"].language.get_sort("Pointer")
    trivial_model = FOProvableStructureTemplate(theory, unfold_depth=unfold_depth)
    goal_model = FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 })

    for candidate, counterexample in CEGISynthesizer().synthesize_for_model_classes(templates, trivial_model, goal_model, debug=False):
        if counterexample is None:
            print(candidate)


sort_pointer = theory_map["HEAP"].language.get_sort("Pointer")

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

#################
#### Lemma 1 ####
#################

# language = theory_map["LIST1"].language.get_sublanguage(
#     ("Pointer",),
#     ("nil", "l"),
#     ("list1", "list"),
# )

# synthesize(
#     theory_map["LIST1"],
#     (
#         Implication(
#             AtomicFormulaTemplate(language, (x,), 0),
#             AtomicFormulaTemplate(language, (x,), 0),
#         ),
#     ),
#     unfold_depth=2,
# )

####################
#### Lemmas 2-4 ####
####################

# language = theory_map["LIST"].language.get_sublanguage(
#     ("Pointer",),
#     ("nil",),
#     ("list", "lseg"),
# )

# synthesize(
#     theory_map["LIST"],
#     (
#         Implication(
#             AtomicFormulaTemplate(language, (x, y), 0),
#             AtomicFormulaTemplate(language, (x, y), 0),
#         ),
#         Implication(
#             Conjunction(
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#             ),
#             AtomicFormulaTemplate(language, (x, y, z), 0),
#         ),
#         Implication(
#             Conjunction(
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#             ),
#             Disjunction(
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#             ),
#         ),
#     ),
#     unfold_depth=1,
# )

##################
#### Lemmas 5 ####
##################

# language = theory_map["LSEGR"].language.get_sublanguage(
#     ("Pointer",),
#     ("nil",),
#     ("lsegr", "lseg"),
# )

# synthesize(
#     theory_map["LSEGR"],
#     (
#         Implication(
#             AtomicFormulaTemplate(language, (x, y), 0),
#             AtomicFormulaTemplate(language, (x, y), 0),
#         ),
#     ),
#     unfold_depth=1,
# )

####################
#### Lemmas 6-8 ####
####################

# language = theory_map["DLIST1"].language.get_sublanguage(
#     ("Pointer",),
#     ("nil", "l"),
#     ("dlist1", "dlist", "dlseg", "list"),
# )

# synthesize(
#     theory_map["DLIST1"],
#     (
#         Implication(
#             AtomicFormulaTemplate(language, (x, y), 0),
#             AtomicFormulaTemplate(language, (x, y), 0),
#         ),
#         Implication(
#             Conjunction(
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#             ),
#             AtomicFormulaTemplate(language, (x, y, z), 0),
#         ),
#     ),
#     unfold_depth=1,
# )

######################
#### Lemmas 10-12 ####
######################

language = theory_map["SLIST1"].language.get_sublanguage(
    ("Pointer",),
    ("nil", "l"),
    ("slist1", "slist"),
)

synthesize(
    theory_map["SLIST1"],
    (
        Implication(
            AtomicFormulaTemplate(language, (x,), 0),
            AtomicFormulaTemplate(language, (x,), 0),
        ),
    ),
    unfold_depth=1,
)

# language = theory_map["SLIST"].language.get_sublanguage(
#     ("Pointer",),
#     ("nil",),
#     ("slist", "slseg", "list"),
# )

# synthesize(
#     theory_map["SLIST1"],
#     (
#         Implication(
#             AtomicFormulaTemplate(language, (x, y), 0),
#             AtomicFormulaTemplate(language, (x, y), 0),
#         ),
#         Implication(
#             Conjunction(
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#                 AtomicFormulaTemplate(language, (x, y, z), 0),
#             ),
#             AtomicFormulaTemplate(language, (x, y, z), 0),
#         ),
#     ),
#     unfold_depth=1,
# )

######################
#### Lemmas 13-14 ####
######################

# language = theory_map["BST"].language.get_sublanguage(
#     ("Pointer",),
#     ("nil", "c", "key"),
#     ("btree", "bst", "leftmost", "le_int", "ne_pointer"),
# )

# synthesize(
#     theory_map["BST"],
#     (
#         Implication(
#             AtomicFormulaTemplate(language, (x,), 0),
#             AtomicFormulaTemplate(language, (x,), 0),
#         ),
#         Implication(
#             Conjunction.from_conjuncts(
#                 AtomicFormulaTemplate(language, (x,), 0),
#                 AtomicFormulaTemplate(language, (x,), 0),
#             ),
#             AtomicFormulaTemplate(language, (x,), 1),
#         ),
#     ),
#     unfold_depth=1,
# )
