from fol import *
from fol.prover import *


theory = Parser.parse_theory(r"""
theory LIST
    sort Pointer

    constant nil: Pointer
    function n: Pointer -> Pointer

    relation list: Pointer
    relation lseg: Pointer Pointer
    relation in_lseg: Pointer Pointer Pointer

    relation eq: Pointer Pointer [smt("(= #1 #2)")]

    fixpoint in_lseg(x, y, z) = not eq(y, z) /\ (eq(x, y) \/ in_lseg(x, n(y), z))
    fixpoint list(x) = eq(x, nil()) \/ (list(n(x)) /\ not in_lseg(x, n(x), nil()))
    fixpoint lseg(x, y) = eq(x, y) \/ (lseg(n(x), y) /\ not in_lseg(x, n(x), y))
end
""")

sort = theory.language.get_sort("Pointer")
assert sort is not None
sort_pointer = sort


def prove(goal_src: str, depth: int) -> None:
    goal = Parser.parse_formula(theory.language, goal_src)
    language, conjuncts = NaturalProof.encode_validity(theory, sort_pointer, goal, depth)

    # for conjunct in conjuncts:
    #     print("conjunct", conjunct)

    uninterp_structure = UninterpretedModelTemplate(language)

    with smt.Solver(name="z3") as solver:
        solver.add_assertion(uninterp_structure.get_constraint())

        for conjunct in conjuncts:
            solver.add_assertion(conjunct.interpret(uninterp_structure, {}))

        if not solver.solve():
            print(f"{goal} is valid")
        else:
            print(f"{goal} is unprovable")

prove(r"(exists x: Pointer, y: Pointer. list(x) /\ list(y) /\ not eq(x, y)) -> exists x: Pointer. list(n(x))", 1)
prove(r"forall x: Pointer. eq(n(x), nil()) -> list(x)", 1)
prove(r"(forall x: Pointer. eq(n(x), x)) -> forall x: Pointer. not eq(x, nil()) -> not list(x)", 2)
prove(r"forall x: Pointer. list(x) -> lseg(x, nil())", 2)
prove(r"not in_lseg(nil(), nil(), nil())", 1)
# prove(r"(forall x2:Pointer. (forall x1:Pointer. (forall x0:Pointer. ((not eq(x1:Pointer, x2:Pointer) /\ (eq(x0:Pointer, x1:Pointer) \/ (in_lseg(nil(), x2:Pointer, x2:Pointer) -> in_lseg(nil(), nil(), nil())))) -> (in_lseg(nil(), x2:Pointer, x2:Pointer) -> in_lseg(nil(), nil(), nil()))))))", 1)