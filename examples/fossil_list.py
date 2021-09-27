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
theory LIST
    sort Pointer

    constant nil: Pointer
    function n: Pointer -> Pointer

    relation list: Pointer
    relation lseg: Pointer Pointer

    relation eq: Pointer Pointer [smt("(= #1 #2)")]

    fixpoint list(x) = eq(x, nil()) \/ list(n(x))
    fixpoint lseg(x, y) = eq(x, y) \/ lseg(n(x), y)
end
""")

sort_pointer = theory.language.get_sort("Pointer")

use_type1_models = True
use_non_fo_provable_lemmas = False

time_fn(lambda:
FOSSIL.prove_lfp(
    theory,
    sort_pointer,
    theory.language.get_sublanguage(
        ("Pointer",),
        ("nil", "n"),
        ("list", "lseg"),
    ),
    Parser.parse_formula(theory.language, r"forall x: Pointer. list(x) -> lseg(x, nil())"),
    natural_proof_depth=1,
    lemma_term_depth=0,
    lemma_formula_depth=0,
    true_counterexample_size_bound=4,
    use_type1_models=use_type1_models,
    use_non_fo_provable_lemmas=use_non_fo_provable_lemmas,
))

time_fn(lambda:
FOSSIL.prove_lfp(
    theory,
    sort_pointer,
    theory.language.get_sublanguage(
        ("Pointer",),
        ("nil", "n"),
        ("list", "lseg", "eq"),
    ),
    Parser.parse_formula(theory.language, r"forall x: Pointer. lseg(x, nil()) -> list(x)"),
    natural_proof_depth=1,
    lemma_term_depth=0,
    lemma_formula_depth=0,
    true_counterexample_size_bound=4,
    use_type1_models=use_type1_models,
    use_non_fo_provable_lemmas=use_non_fo_provable_lemmas,
))

time_fn(lambda:
FOSSIL.prove_lfp(
    theory.remove_fixpoint_definition("list"),
    sort_pointer,
    theory.language.get_sublanguage(
        ("Pointer",),
        (),
        ("lseg",),
    ),
    Parser.parse_formula(theory.language, r"forall x: Pointer, y: Pointer, z: Pointer. lseg(x, y) /\ lseg(y, z) -> lseg(x, z)"),
    natural_proof_depth=2,
    lemma_term_depth=0,
    lemma_formula_depth=1,
    true_counterexample_size_bound=4,
    additional_free_vars=1,
    use_type1_models=use_type1_models,
    use_non_fo_provable_lemmas=use_non_fo_provable_lemmas,
))
