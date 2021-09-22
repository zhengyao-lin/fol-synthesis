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

theory LISTLEN extending LIST INT
    constant l: Int

    // list of length l
    relation listlen: Pointer Int
    fixpoint listlen(x, l) =
        (x = nil() /\ l = zero()) \/
        (
            x != nil() /\
            listlen(next(x), minus(l, one())) /\
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

theory DLISTLEN extending DLIST INT
    constant l: Int

    // list of length l
    relation dlistlen: Pointer Int
    fixpoint dlistlen(x, l) =
        (x = nil() /\ l = zero()) \/ (next(x) = nil() /\ l = one()) \/
        (
            prev(next(x)) = x /\
            dlistlen(next(x), minus(l, one())) /\
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

theory SLISTLEN extending SLIST INT
    constant l: Int

    // list of length l
    relation slistlen: Pointer Int
    fixpoint slistlen(x, l) =
        (x = nil() /\ l = zero()) \/
        (next(x) = nil() /\ l = one()) \/
        (
            le_int(key(x), key(next(x))) /\
            slistlen(next(x), minus(l, one())) /\
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

sort_pointer = theory_map["HEAP"].language.get_sort("Pointer")

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

###################
#### Lemma 1-4 ####
###################

theory = theory_map["LISTLEN"]
language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "l"),
    ("listlen", "list", "lseg"),
)
listlen_symbol = theory.language.get_relation_symbol("listlen")

for candidate, counterexample in CEGISynthesizer().synthesize_for_model_classes(
    (
        Implication(
            AtomicFormulaTemplate(language, (x,), 0),
            AtomicFormulaTemplate(language, (x,), 0),
        ),
        Implication(
            AtomicFormulaTemplate(language, (x, y), 0),
            AtomicFormulaTemplate(language, (x, y), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y, z), 0),
                AtomicFormulaTemplate(language, (x, y, z), 0),
            ),
            AtomicFormulaTemplate(language, (x, y, z), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y, z), 0),
                AtomicFormulaTemplate(language, (x, y, z), 0),
            ),
            Disjunction(
                AtomicFormulaTemplate(language, (x, y, z), 0),
                AtomicFormulaTemplate(language, (x, y, z), 0),
            ),
        ),
    ),
    trivial_model=FOProvableStructureTemplate(theory, unfold_depth=1),
    goal_model=FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 }, fixpoint_bounds={ listlen_symbol: 1 }),
    debug=False,
):
    if counterexample is None: print(candidate)

##################
#### Lemmas 5 ####
##################

theory = theory_map["LSEGR"]
language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil",),
    ("lsegr", "lseg"),
)

for candidate, counterexample in CEGISynthesizer().synthesize_for_model_classes(
    (
        Implication(
            AtomicFormulaTemplate(language, (x,), 0),
            AtomicFormulaTemplate(language, (x,), 0),
        ),
    ),
    trivial_model=FOProvableStructureTemplate(theory, unfold_depth=1),
    goal_model=FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 }),
    debug=False,
):
    if counterexample is None: print(candidate)

####################
#### Lemmas 6-8 ####
####################

theory = theory_map["DLISTLEN"]
language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "l"),
    ("dlistlen", "dlist", "dlseg", "list"),
)
dlistlen_symbol = theory.language.get_relation_symbol("dlistlen")

for candidate, counterexample in CEGISynthesizer().synthesize_for_model_classes(
    (
        Implication(
            AtomicFormulaTemplate(language, (x, y), 0),
            AtomicFormulaTemplate(language, (x, y), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y, z), 0),
                AtomicFormulaTemplate(language, (x, y, z), 0),
            ),
            AtomicFormulaTemplate(language, (x, y, z), 0),
        ),
    ),
    trivial_model=FOProvableStructureTemplate(theory, unfold_depth=1),
    goal_model=FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 }, fixpoint_bounds={ dlistlen_symbol: 1 }),
    debug=False,
):
    if counterexample is None: print(candidate)

######################
#### Lemmas 10-12 ####
######################

theory = theory_map["SLISTLEN"]
language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "l"),
    ("slistlen", "slist", "slseg", "list"),
)
slistlen_symbol = theory.language.get_relation_symbol("slistlen")

for candidate, counterexample in CEGISynthesizer().synthesize_for_model_classes(
    (
        Implication(
            AtomicFormulaTemplate(language, (x, y), 0),
            AtomicFormulaTemplate(language, (x, y), 0),
        ),
        Implication(
            Conjunction(
                AtomicFormulaTemplate(language, (x, y, z), 0),
                AtomicFormulaTemplate(language, (x, y, z), 0),
            ),
            AtomicFormulaTemplate(language, (x, y, z), 0),
        ),
    ),
    trivial_model=FOProvableStructureTemplate(theory, unfold_depth=1),
    goal_model=FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 }, fixpoint_bounds={ slistlen_symbol: 1 }),
    debug=False,
):
    if counterexample is None: print(candidate)

######################
#### Lemmas 13-14 ####
######################

theory = theory_map["BST"]
language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "c", "key"),
    ("btree", "bst", "leftmost", "le_int", "ne_pointer"),
)
leftmost_symbol = theory.language.get_relation_symbol("leftmost")

for candidate, counterexample in CEGISynthesizer().synthesize_for_model_classes(
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
            AtomicFormulaTemplate(language, (x, y), 1),
        ),
    ),
    trivial_model=FOProvableStructureTemplate(theory, unfold_depth=1),
    goal_model=FiniteLFPModelTemplate(theory, size_bounds={ sort_pointer: 4 }, fixpoint_bounds={ leftmost_symbol: 2 }),
    debug=False,
):
    if counterexample is None: print(candidate)
