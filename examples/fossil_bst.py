from typing import Callable, Any

import sys
import time

from synthesis import *
from synthesis.fol.fossil import FOSSIL


def time_fn(f: Callable[..., Any]) -> None:
    begin = time.time()
    f()
    print(f"elapsed: {time.time() - begin} s", file=sys.stderr, flush=True)


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

    relation le_int: Int Int [smt("(<= #1 #2)")]
    relation eq_int: Int Int [smt("(= #1 #2)")]

    relation eq_pointer: Pointer Pointer [smt("(= #1 #2)")]
    relation ne_pointer: Pointer Pointer [smt("(not (= #1 #2))")]
    
    fixpoint btree(x) =
        eq_pointer(x, nil()) \/
        (eq_pointer(left(x), nil()) /\ eq_pointer(right(x), nil())) \/
        (btree(left(x)) /\ btree(right(x)))

    fixpoint bst(x) =
        eq_pointer(x, nil()) \/
        (eq_pointer(left(x), nil()) /\ eq_pointer(right(x), nil())) \/
        (
            le_int(key(left(x)), key(x)) /\
            le_int(key(x), key(right(x))) /\
            bst(left(x)) /\
            bst(right(x))
        )

    fixpoint leftmost(x, v) =
        not eq_pointer(x, nil()) /\
        ((eq_pointer(left(x), nil()) /\ eq_int(key(x), v)) \/ leftmost(left(x), v))
end
""")

sort_pointer = theory.language.get_sort("Pointer")

params = {
    "use_type1_models": False,
    "use_non_fo_provable_lemmas": True,
}

time_fn(lambda:
FOSSIL.prove_lfp(
    theory,
    sort_pointer,
    theory.language.get_sublanguage(
        ("Pointer",),
        (),
        ("bst", "btree"),
    ),
    Parser.parse_formula(theory.language, r"forall x: Pointer. bst(x) -> btree(x)"),
    natural_proof_depth=1,
    lemma_term_depth=0,
    lemma_formula_depth=0,
    true_counterexample_size_bound=6,
    **params,
))
