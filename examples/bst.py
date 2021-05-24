from z3 import *
from synthesis import *


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language(
        { "nil": 0, "left": 1, "right": 1, "key": 1 },
        {
            "btree": 1,
            "bst": 1,
            # "le": 2,
            # "leftmost": 2
        })
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    bst1_domain = { 0, -1, 2, 3, 4, -5, 6 }
    bst1 = FiniteStructure.create(
        env,
        language,
        bst1_domain,
        {
            "nil": 0,
            "left": {
                0: 0,
                -1: 3,
                2: 4,
                3: 0,
                4: 0,
                -5: 4,
                6: 3,
            },
            "right": {
                0: 0,
                -1: 4,
                2: 3,
                3: 0,
                4: 0,
                -5: 4,
                6: 3,
            },
            "key": {
                0: 0,
                -1: 0,
                2: 0,
                3: -100,
                4: 100,
                -5: 100,
                6: -100,
            },
        },
        {
            "btree": { 0, -1, 2, 3, 4 },
            "bst": { 0, -1, 3, 4 },
            "leftmost": {
                (0, 0),
                (-1, -100),
                (2, 100),
                (3, -100),
                (4, 100),
                (5, 100),
                (6, -100),
            },
            "le": lambda x, y: x <= y,
        },
    )

    synthesizer.add_example(bst1)

    ################################
    # construct the counterexample #
    ################################
    nil = 0
    left = FreshFunction(IntSort(), IntSort())
    right = FreshFunction(IntSort(), IntSort())
    key = FreshFunction(IntSort(), IntSort())

    btree_unroll0 = FreshFunction(IntSort(), BoolSort())
    bst_unroll0 = FreshFunction(IntSort(), BoolSort())
    in_bst_unroll0 = FreshFunction(IntSort(), IntSort(), BoolSort())
    leftmost_unroll0 = FreshFunction(IntSort(), IntSort(), BoolSort())

    in_bst_unroll1 = lambda x, y: z3.If(
        y == nil,
        False,
        z3.Or(
            x == y,
            in_bst_unroll0(x, left(y)),
            in_bst_unroll0(x, right(y)),
        )
    )

    btree_unroll1 = lambda x: z3.Or(
        z3.Or(
            x == nil,
            z3.And(left(x) == nil, right(x) == nil),
        ),
        z3.And(
            btree_unroll0(left(x)),
            btree_unroll0(right(x)),
            z3.Not(in_bst_unroll1(x, left(x))),
            z3.Not(in_bst_unroll1(x, right(x))),
        ),
    )

    bst_unroll1 = lambda x: z3.Or(
        z3.Or(
            x == nil,
            z3.And(left(x) == nil, right(x) == nil),
        ),
        z3.And(
            key(left(x)) <= key(x),
            key(x) <= key(right(x)),
            bst_unroll0(left(x)),
            bst_unroll0(right(x)),
            z3.Not(in_bst_unroll1(x, left(x))),
            z3.Not(in_bst_unroll1(x, right(x))),
        ),
    )

    leftmost_unroll1 = lambda x, v: z3.Or(
        z3.And(left(x) == nil, key(x) == v),
        z3.And(left(x) != nil, leftmost_unroll0(left(x), v))
    )

    counterexample = Structure(
        IntSort(),
        {
            "nil": lambda: nil,
            "left": left,
            "right": right,
            "key": key,
        },
        {
            "btree": btree_unroll1,
            "bst": bst_unroll1,
            "leftmost": leftmost_unroll1,
            "le": lambda x, y: x <= y,
        },
    )

    synthesizer.add_counterexample(counterexample, tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)))

    return synthesizer.synthesize()


def main():
    for formula in synthesize(term_depth=0, max_num_vars=2, min_num_hypotheses=0, max_num_hypotheses=2, allow_equality_in_conclusion=True):
        print(formula)


if __name__ == "__main__":
    main()
