from z3 import *
from synthesis import *

set_param("parallel.enable", True)
set_param("parallel.threads.max", 4)


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language(
        { "nil": 0, "left": 1, "right": 1, "key": 1 },
        {
            "btree": 1,
            "bst": 1,
            "le": 2,
            "leftmost": 2
        })
    expanded_language = language.expand(
        {},
        { "in_bst": 2 },
    )
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    # bst1_domain = { 0, -1, 2, 3, 4, -5, 6 }
    # bst1 = FiniteConcreteStructure.create(
    #     env,
    #     language,
    #     bst1_domain,
    #     {
    #         "nil": 0,
    #         "left": {
    #             0: 0,
    #             -1: 3,
    #             2: 4,
    #             3: 0,
    #             4: 0,
    #             -5: 4,
    #             6: 3,
    #         },
    #         "right": {
    #             0: 0,
    #             -1: 4,
    #             2: 3,
    #             3: 0,
    #             4: 0,
    #             -5: 4,
    #             6: 3,
    #         },
    #         "key": {
    #             0: 0,
    #             -1: 0,
    #             2: 0,
    #             3: -100,
    #             4: 100,
    #             -5: 100,
    #             6: -100,
    #         },
    #     },
    #     {
    #         "btree": { 0, -1, 2, 3, 4 },
    #         "bst": { 0, -1, 3, 4 },
    #         "leftmost": {
    #             (0, 0),
    #             (-1, -100),
    #             (2, 100),
    #             (3, -100),
    #             (4, 100),
    #             (5, 100),
    #             (6, -100),
    #         },
    #         "le": lambda x, y: x <= y,
    #     },
    # )

    # synthesizer.add_example(bst1)

    nil = lambda structure: structure.eval_function("nil", ())
    left = lambda structure, x: structure.eval_function("left", (x,))
    right = lambda structure, x: structure.eval_function("right", (x,))
    key = lambda structure, x: structure.eval_function("key", (x,))
    
    in_bst = lambda structure, x, y: structure.eval_relation("in_bst", (x, y))
    btree = lambda structure, x: structure.eval_relation("btree", (x,))
    bst = lambda structure, x: structure.eval_relation("bst", (x,))
    leftmost = lambda structure, x, y: structure.eval_relation("leftmost", (x, y))

    in_bst_defn = lambda structure, x, y: z3.If(
        y == nil(structure),
        False,
        z3.Or(
            x == y,
            in_bst(structure, x, left(structure, y)),
            in_bst(structure, x, right(structure, y)),
        ),
    )

    btree_defn = lambda structure, x: z3.Or(
        z3.Or(
            x == nil(structure),
            z3.And(left(structure, x) == nil(structure), right(structure, x) == nil(structure)),
        ),
        z3.And(
            btree(structure, left(structure, x)),
            btree(structure, right(structure, x)),
            z3.Not(in_bst(structure, x, left(structure, x))),
            z3.Not(in_bst(structure, x, right(structure, x))),
        ),
    )

    bst_defn = lambda structure, x: z3.Or(
        z3.Or(
            x == nil(structure),
            z3.And(left(structure, x) == nil(structure), right(structure, x) == nil(structure)),
        ),
        z3.And(
            key(structure, left(structure, x)) <= key(structure, x),
            key(structure, x) <= key(structure, right(structure, x)),
            bst(structure, left(structure, x)),
            bst(structure, right(structure, x)),
            z3.Not(in_bst(structure, x, left(structure, x))),
            z3.Not(in_bst(structure, x, right(structure, x))),
        ),
    )

    leftmost_defn = lambda structure, x, y: z3.Or(
        z3.And(left(structure, x) == nil(structure), key(structure, x) == y),
        z3.And(left(structure, x) != nil(structure), leftmost(structure, left(structure, x), y))
    )

    ################################
    # construct the counterexample #
    ################################
    syn_counterexample_unroll0 = Structure(
        IntSort(),
        expanded_language,
        {
            "nil": (lambda nil: lambda: nil)(FreshInt()),
            "left": FreshFunction(IntSort(), IntSort()),
            "right": FreshFunction(IntSort(), IntSort()),
            "key": FreshFunction(IntSort(), IntSort()),
        },
        {
            "in_bst": FreshFunction(IntSort(), IntSort(), BoolSort()),
            "btree": FreshFunction(IntSort(), BoolSort()),
            "bst": FreshFunction(IntSort(), BoolSort()),
            "leftmost": FreshFunction(IntSort(), IntSort(), BoolSort()),
            "le": lambda x, y: x <= y,
        },
    )

    syn_counterexample_unroll1 = Structure(
        IntSort(),
        expanded_language,
        syn_counterexample_unroll0.function_interprets,
        {
            "in_bst": lambda x, y: in_bst_defn(syn_counterexample_unroll0, x, y),
            "btree": lambda x: btree_defn(syn_counterexample_unroll0, x),
            "bst": lambda x: bst_defn(syn_counterexample_unroll0, x),
            "leftmost": lambda x, y: leftmost_defn(syn_counterexample_unroll0, x, y),
            "le": lambda x, y: x <= y,
        },
    )

    syn_counterexample_unroll2 = Structure(
        IntSort(),
        expanded_language,
        syn_counterexample_unroll1.function_interprets,
        {
            "in_bst": lambda x, y: in_bst_defn(syn_counterexample_unroll1, x, y),
            "btree": lambda x: btree_defn(syn_counterexample_unroll1, x),
            "bst": lambda x: bst_defn(syn_counterexample_unroll1, x),
            "leftmost": lambda x, y: leftmost_defn(syn_counterexample_unroll1, x, y),
            "le": lambda x, y: x <= y,
        },
    )

    synthesizer.set_synthesis_counterexample(syn_counterexample_unroll2, tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)))

    ver_counterexample = FiniteSymbolicStructure.create(
        env,
        expanded_language,
        7,
        function_overrides={},
        relation_overrides={
            "le": lambda x, y: x <= y,
        },
    )
    synthesizer.set_verification_counterexample(ver_counterexample)

    for x, y in ver_counterexample.iterate_universe(2):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("in_bst", (x, y)) == \
            in_bst_defn(ver_counterexample, x, y),
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("btree", (x,)) == \
            btree_defn(ver_counterexample, x),
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("bst", (x,)) == \
            bst_defn(ver_counterexample, x),
        )

    for x, y in ver_counterexample.iterate_universe(2):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("leftmost", (x, y)) == \
            leftmost_defn(ver_counterexample, x, y),
        )

    return synthesizer.synthesize()


def main():
    for formula in synthesize(
        hypothesis_term_depth=0,
        conclusion_term_depth=1,
        max_num_vars=2,
        min_num_hypotheses=0,
        max_num_hypotheses=2,
        allow_equality_in_conclusion=False,
    ):
        print(formula)


if __name__ == "__main__":
    main()
