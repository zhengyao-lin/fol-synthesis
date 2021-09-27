from typing import Iterable, Any

from synthesis import *
from synthesis.fol.fossil import FOSSIL


theory_map = Parser.parse_theories(r"""
theory HEAP
    sort Pointer
end

theory KEYED-HEAP extending HEAP INT
    function key: Pointer -> Int
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
    constant nil: Pointer
    function next: Pointer -> Pointer
    function prev: Pointer -> Pointer
end

theory LIST extending LIST-BASE HEAP
    relation list: Pointer
    relation lseg: Pointer Pointer

    fixpoint list(x) = x = nil() \/ list(next(x))
    fixpoint lseg(x, y) = x = y \/ lseg(next(x), y)
end

theory EVEN-ODD extending LIST
    relation odd_list: Pointer
    relation even_list: Pointer

    fixpoint odd_list(x) = x != nil() /\ even_list(next(x))
    fixpoint even_list(x) = x = nil() \/ odd_list(next(x))
end

theory DLIST extending LIST-BASE
    relation dlist: Pointer
    relation dlseg: Pointer Pointer

    fixpoint dlist(x) = x = nil() \/ next(x) = nil() \/ (prev(next(x)) = x /\ dlist(next(x)))
    fixpoint dlseg(x, y) = x = y \/ (prev(next(x)) = x /\ dlseg(next(x), y))
end

theory SLIST extending LIST-BASE KEYED-HEAP INT
    relation slist: Pointer
    relation slseg: Pointer Pointer

    fixpoint slist(x) =
        x = nil() \/ next(x) = nil() \/ (le_int(key(x), key(next(x))) /\ slist(next(x)))

    fixpoint slseg(x, y) =
        x = y \/ (le_int(key(x), key(next(x))) /\ slseg(next(x), y))
end

theory SDLIST extending LIST-BASE KEYED-HEAP
    relation sdlist: Pointer
    relation sdlseg: Pointer Pointer

    fixpoint sdlist(x) = x = nil() \/ next(x) = nil() \/ (le_int(key(x), key(next(x))) /\ prev(next(x)) = x /\ sdlist(next(x)))
    fixpoint sdlseg(x, y) = x = y \/ (prev(next(x)) = x /\ sdlseg(next(x), y))
end

theory SLIST-LIST extending SLIST LIST end
theory DLIST-LIST extending DLIST LIST end
theory SDLIST-LIST extending SDLIST LIST end
theory SDLIST-DLIST extending SDLIST DLIST end

theory BST extending HEAP INT
    constant nil: Pointer
    function left: Pointer -> Pointer
    function right: Pointer -> Pointer
    function key: Pointer -> Int
    
    relation btree: Pointer
    relation bst: Pointer
    
    fixpoint btree(x) =
        x = nil() \/
        (left(x) = nil() /\ right(x) = nil()) \/
        (btree(left(x)) /\ btree(right(x)))

    fixpoint bst(x) =
        x = nil() \/
        (left(x) = nil() /\ right(x) = nil()) \/
        (
            le_int(key(left(x)), key(x)) /\
            le_int(key(x), key(right(x))) /\
            bst(left(x)) /\
            bst(right(x))
        )
end
""")


def prove(
    theory_name: str,
    foreground_sort_name: str,
    function_names: Iterable[str],
    relation_names: Iterable[str],
    statement: str,
    **other_params: Any,
) -> Tuple[Formula, ...]:
    """
    Try to prove a statement in the LFP semantics
    using increasingly large lemmas

    If proved, return all the lemmas used
    """

    assert theory_name in theory_map, \
           f"theory {theory_name} not found"
    theory = theory_map[theory_name]

    sublanguage = theory.language.get_sublanguage(
        (foreground_sort_name,),
        tuple(function_names),
        tuple(relation_names),
    )

    foreground_sort = sublanguage.get_sort(foreground_sort_name)

    # we have four parameters to increase:
    # given iteration number i (starting from 0)
    # natural_proof_depth = <init> + i
    # lemma_term_depth = <init> + i // 2
    # lemma_formula_depth = <init> + i
    # true_counterexample_size_bound = <init> + i // 3
    natural_proof_depth_init = other_params.get("natural_proof_depth", 1)
    lemma_term_depth_init = other_params.get("lemma_term_depth", 0)
    lemma_formula_depth_init = other_params.get("lemma_formula_depth", 0)
    true_counterexample_size_bound_init = other_params.get("true_counterexample_size_bound", 4)

    if "natural_proof_depth" in other_params:
        del other_params["natural_proof_depth"]

    if "lemma_term_depth" in other_params:
        del other_params["lemma_term_depth"]

    if "lemma_formula_depth" in other_params:
        del other_params["lemma_formula_depth"]

    if "true_counterexample_size_bound" in other_params:
        del other_params["true_counterexample_size_bound"]

    lemmas = tuple(other_params.get("initial_lemmas", ()))
    if "initial_lemmas" in other_params:
        del other_params["initial_lemmas"]

    iteration = 0

    while True:
        natural_proof_depth = natural_proof_depth_init + iteration // 2
        lemma_term_depth = lemma_term_depth_init + iteration // 2
        lemma_formula_depth = lemma_formula_depth_init + iteration
        true_counterexample_size_bound = true_counterexample_size_bound_init + iteration // 2

        print(f"iteration {iteration}: params = ({natural_proof_depth}, {lemma_term_depth}, {lemma_formula_depth}, {true_counterexample_size_bound})")

        result, lemmas = FOSSIL.prove_lfp(
            theory,
            foreground_sort,
            sublanguage,
            Parser.parse_formula(theory.language, statement),
            natural_proof_depth=natural_proof_depth,
            lemma_term_depth=lemma_term_depth,
            lemma_formula_depth=lemma_formula_depth,
            true_counterexample_size_bound=true_counterexample_size_bound,
            initial_lemmas=lemmas,
            **other_params,
        )

        if result:
            return lemmas

        iteration += 1


# prove("LIST", "Pointer", ("nil", "next"), ("list", "lseg"),
#       r"forall x: Pointer. list(x) -> lseg(x, nil())")

prove("LIST", "Pointer", ("next",), ("list", "lseg"),
      r"forall x: Pointer, y: Pointer. lseg(x, y) -> lseg(next(x), next(y))",
      natural_proof_depth=2,
      lemma_term_depth=1)

prove("LIST", "Pointer", ("nil", "next"), ("list", "lseg"),
      r"forall x: Pointer. lseg(x, nil()) -> list(x)")

prove("LIST", "Pointer", ("nil", "next"), ("list", "lseg"),
      r"forall x: Pointer, y: Pointer, z: Pointer. lseg(x, y) /\ lseg(y, z) -> lseg(x, z)",
      natural_proof_depth=2,
      additional_free_vars=1)

prove("EVEN-ODD", "Pointer", ("nil", "next"), ("list", "even_list", "odd_list"),
      r"forall x: Pointer. list(x) -> even_list(x) \/ odd_list(x)")

prove("BST", "Pointer", (), ("bst", "btree"), r"forall x: Pointer. bst(x) -> btree(x)")

prove("DLIST-LIST", "Pointer", (), ("dlist", "list"), r"forall x: Pointer. dlist(x) -> list(x)")

prove("SLIST-LIST", "Pointer", (), ("slist", "list"), r"forall x: Pointer. slist(x) -> list(x)")

prove("SLIST", "Pointer", (), ("slist", "slseg"), r"forall x: Pointer, y: Pointer. slseg(x, y) -> (slist(y) -> slist(x))")

prove("SDLIST-DLIST", "Pointer", (), ("sdlist", "dlist"), r"forall x: Pointer. sdlist(x) -> dlist(x)")
