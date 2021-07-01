from z3 import *
from synthesis import *


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language(
        { "nil": 0, "next": 1, "prev": 1 },
        {
            "list": 1,
            "dlist": 1,
        })
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    list1_domain = { 0, 1, 2, 3, 4 }
    list1 = FiniteConcreteStructure.create(
        env,
        language,
        list1_domain,
        {
            "nil": 0,
            "next": {
                0: 0,
                1: 0,
                2: 1,
                3: 3,
                4: 3,
            },
            "prev": {
                0: 0,
                1: 2,
                2: 2,
                3: 4,
                4: 4,
            }
        },
        {
            "list": { 0, 1, 2 },
            "dlist": { 0, 1 },
        },
    )

    synthesizer.add_example(list1)

    ################################
    # construct the counterexample #
    ################################
    nil = 0
    n = FreshFunction(IntSort(), IntSort())
    p = FreshFunction(IntSort(), IntSort())
    list_unroll0 = FreshFunction(IntSort(), BoolSort())
    dlist_unroll0 = FreshFunction(IntSort(), BoolSort())
    in_lsegf_unroll0 = FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort())
    in_lsegb_unroll0 = FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort())
    
    in_lsegf_unroll1 = lambda x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, in_lsegf_unroll0(x, n(y), z))
        )

    in_lsegb_unroll1 = lambda x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, in_lsegb_unroll0(x, p(y), z))
        )

    list_unroll1 = lambda x: Or(
        x == nil,
        And(
            Not(x == nil),
            list_unroll0(n(x)),
            Not(in_lsegf_unroll1(x, n(x), nil)),
        ),
    )

    dlist_unroll1 = lambda x: Or(
        Or(x == nil, n(x) == nil),
        And(
            Not(x == nil), Not(n(x) == nil),
            p(n(x)) == x,
            dlist_unroll0(n(x)),
            Not(in_lsegf_unroll1(x, n(x), nil)),
            Not(in_lsegb_unroll1(x, p(x), nil)),
        ),
    )

    counterexample = Structure(
        IntSort(),
        {
            "nil": lambda: nil,
            "next": n,
            "prev": p,
        },
        {
            "list": list_unroll1,
            "dlist": dlist_unroll1,
        },
    )

    synthesizer.add_counterexample(counterexample, tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)))

    return synthesizer.synthesize()


def main():
    for formula in synthesize(term_depth=1, max_num_vars=3, max_num_hypotheses=2, allow_equality_in_conclusion=True):
        print(formula)


if __name__ == "__main__":
    main()
