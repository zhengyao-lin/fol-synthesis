from synthesis import *
from synthesis.fol.prover import NaturalProof


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
    // fixpoint list(x) = eq(x, nil()) \/ (list(n(x)) /\ not in_lseg(x, n(x), nil()))
    fixpoint lseg(x, y) = eq(x, y) \/ (lseg(n(x), y) /\ not in_lseg(x, n(x), y))

    // axiom forall x: Pointer, y: Pointer, z: Pointer. in_lseg(x, y, z) /\ lseg(y, z) -> lseg(x, z)
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

# prove(r"(exists x: Pointer, y: Pointer. list(x) /\ list(y) /\ not eq(x, y)) -> exists x: Pointer. list(n(x))", 1)
# prove(r"forall x: Pointer. eq(n(x), nil()) -> list(x)", 1)
# prove(r"(forall x: Pointer. eq(n(x), x)) -> forall x: Pointer. not eq(x, nil()) -> not list(x)", 2)
# prove(r"forall x: Pointer. list(x) -> lseg(x, nil())", 2)
# prove(r"not in_lseg(nil(), nil(), nil())", 1)

# prove(r"(forall x3:Pointer. (forall x2:Pointer. ((eq(x2:Pointer, x3:Pointer) \/ (lseg(x3, n(x2)) /\ (forall x0:Pointer. (lseg(x3:Pointer, x0:Pointer) -> lseg(n(x2:Pointer), x0:Pointer))) /\ not in_lseg(x2:Pointer, n(x2:Pointer), x3:Pointer))) -> (forall x0:Pointer. (lseg(x3:Pointer, x0:Pointer) -> lseg(x2:Pointer, x0:Pointer))))))", 3)
# prove(r"(forall x2:Pointer. (forall x1:Pointer. (forall x0:Pointer. ((not eq(x1:Pointer, x2:Pointer) /\ (eq(x0:Pointer, x1:Pointer) \/ (in_lseg(nil(), x2:Pointer, x2:Pointer) -> in_lseg(nil(), nil(), nil())))) -> (in_lseg(nil(), x2:Pointer, x2:Pointer) -> in_lseg(nil(), nil(), nil()))))))", 1)

# prove(r"(forall x2:Pointer. (forall x1:Pointer. ((eq(x1:Pointer, x2:Pointer) \/ (lseg(n(x1), x2) /\ (list(x2:Pointer) -> list(n(x1:Pointer))) /\ not in_lseg(x1:Pointer, n(x1:Pointer), x2:Pointer))) -> (list(x2:Pointer) -> list(x1:Pointer)))))", 2)

# this one needs a lemma: forall x: Pointer, y: Pointer, z: Pointer. in_lseg(x, y, z) /\ lseg(y, z) -> lseg(x, z)
prove(r"""
forall x: Pointer, y: Pointer.
eq(x, y) \/ ((forall z: Pointer. lseg(y, z) -> lseg(n(x), z)) /\ not in_lseg(x, n(x), y))
->
forall z: Pointer. lseg(y, z) -> lseg(x, z)
""", 2)

# prove(r"""
# forall x: Pointer, y: Pointer.
# eq(x, y) \/ ((forall z: Pointer. lseg(y, z) -> not in_lseg(n(x), n(n(x)), z)) /\ not in_lseg(x, n(x), y))
# ->
# forall z: Pointer. lseg(y, z) -> not in_lseg(x, n(x), z)
# """, 2)


# prove(r"""
# forall x: Pointer, y: Pointer, z: Pointer.
# not eq(y, z) /\ (eq(x, y) \/ (lseg(n(y), z) -> lseg(x, z)))
# -> lseg(y, z)
# -> lseg(x, z)
# """, 1)
