from typing import Any

from synthesis import smt
from synthesis.fol import *
from synthesis.synthesis import *
from synthesis.parser.parser import Parser


theory = Parser.parse_theory(r"""
theory DLIST
    sort Pointer
    sort Int [smt("Int")]
    // sort Set [smt("(Array Int Bool)")]

    constant c: Int

    constant nil: Pointer
    function prev: Pointer -> Pointer
    function next: Pointer -> Pointer

    function key: Pointer -> Int
    relation in_keys: Int Pointer

    fixpoint in_keys(v, x) =
        not eq_pointer(x, nil()) /\
        (eq_int(v, key(x)) \/ in_keys(v, next(x)))

    // constant emp: Set              [smt("((as const (Set Int)) false)")]
    // function union: Set Set -> Set [smt("(union #1 #2)")]

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
    // relation eq_set: Set Set [smt("(= #1 #2)")]

    fixpoint in_lsegf(x, y, z) = not eq_pointer(y, z) /\ (eq_pointer(x, y) \/ in_lsegf(x, next(y), z))
    fixpoint in_lsegb(x, y, z) = not eq_pointer(y, z) /\ (eq_pointer(x, z) \/ in_lsegb(x, y, prev(z)))

    fixpoint in_listf(x, y) =
        not eq_pointer(y, nil()) /\
        (eq_pointer(x, y) \/ in_listf(x, next(y)))

    fixpoint in_listb(x, y) =
        not eq_pointer(y, nil()) /\
        (eq_pointer(x, y) \/ in_listb(x, prev(y)))

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


def test1():
    language = theory.language.get_sublanguage(
        ("Pointer", "Int"),
        ("nil", "next", "prev"),
        ("list", "dlist", "dlseg"),
    )

    x = Variable("x", sort_pointer)
    y = Variable("y", sort_pointer)

    # free variables are universally quantified
    template = Implication(
        Conjunction(
            AtomicFormulaVariable(language, (x, y), 0),
            AtomicFormulaVariable(language, (x, y), 0),
        ),
        AtomicFormulaVariable(language, (x, y), 0),
    )

    model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 5 })

    for _ in CEIGSynthesizer(theory, template, model_var, 2).synthesize(): ...


def test2():
    language = theory.language.get_sublanguage(
        ("Pointer", "Int"),
        ("nil", "next", "prev", "c"),
        ("dlist", "rev", "in_keys"),
    )

    c = Application(language.get_function_symbol("c"), ())
    in_keys = lambda x, y: RelationApplication(language.get_relation_symbol("in_keys"), (x, y))
    rev = lambda x, y: RelationApplication(language.get_relation_symbol("rev"), (x, y))
    dlist = lambda x: RelationApplication(language.get_relation_symbol("dlist"), (x,))

    x = Variable("x", sort_pointer)
    y = Variable("y", sort_pointer)

    # free variables are universally quantified
    template = Implication(
        Conjunction(
            Conjunction(
                dlist(x),
                dlist(y),
            ),
            # AtomicFormulaVariable(language, (x, y), 0),
            rev(x, y),
        ),
        Equivalence(
            in_keys(c, x),
            in_keys(c, y),
            # AtomicFormulaVariable(language, (x, y), 0),
            # AtomicFormulaVariable(language, (x, y), 0),
        ),
    )

    model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 4 })

    for _ in CEIGSynthesizer(theory, template, model_var, 0).synthesize(): ...


test1()
# test2()
