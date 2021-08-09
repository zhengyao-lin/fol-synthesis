from fol import *
from fol.fossil import FOSSIL


theory = Parser.parse_theory(r"""
theory LIST
    sort Pointer

    constant nil: Pointer
    function n: Pointer -> Pointer

    relation list: Pointer
    relation odd_list: Pointer
    relation even_list: Pointer

    relation eq: Pointer Pointer [smt("(= #1 #2)")]

    fixpoint list(x) = eq(x, nil()) \/ list(n(x))
    fixpoint odd_list(x) = not eq(x, nil()) /\ even_list(n(x))
    fixpoint even_list(x) = eq(x, nil()) \/ odd_list(n(x))
end
""")

sort_pointer = theory.language.get_sort("Pointer")
assert sort_pointer is not None

FOSSIL.prove_lfp(
    theory,
    sort_pointer,
    theory.language.get_sublanguage(
        ("Pointer",),
        ("nil", "n"),
        ("list", "even_list", "odd_list"),
    ),
    Parser.parse_formula(theory.language, r"forall x: Pointer. list(x) -> even_list(x) \/ odd_list(x)"),
    natural_proof_depth=1,
    lemma_term_depth=0,
    lemma_formula_depth=1,
    true_counterexample_size_bound=5,
)
