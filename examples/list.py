from z3 import *
from synthesis import *


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language({ "nil": 0, "n": 1 }, { "list": 1, "lseg": 2 })
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    list1_domain = { 0, 1, 2, 3, 4 }
    list1 = FiniteStructure.create(
        env,
        language,
        list1_domain,
        {
            "nil": 0,
            "n": {
                0: 0,
                1: 0,
                2: 1,
                3: 3,
                4: 3,
            },
        },
        {
            "list": { 0, 1, 2 },
            "lseg": { (x, y) for x in list1_domain for y in list1_domain if 2 >= x >= y }.union({
                (3, 3),
                (4, 3),
                (4, 4),
            })
        },
    )

    synthesizer.add_example(list1)

    ################################
    # construct the counterexample #
    ################################
    nil = 0
    n = FreshFunction(IntSort(), IntSort())
    list_unroll0 = FreshFunction(IntSort(), BoolSort())
    lseg_unroll0 = FreshFunction(IntSort(), IntSort(), BoolSort())
    in_lseg_unroll0 = FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort())

    in_lseg_unroll1 = lambda x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, in_lseg_unroll0(x, n(y), z))
        )

    list_unroll1 = lambda x: Or(
        x == nil,
        And(
            Not(x == nil),
            list_unroll0(n(x)),
            Not(in_lseg_unroll1(x, n(x), nil)),
        ),
    )

    lseg_unroll1 = lambda x, y: Or(
        x == y,
        And(
            Not(x == y),
            lseg_unroll0(n(x), y),
            Not(in_lseg_unroll1(x, n(x), y)),
        ),
    )

    counterexample = Structure(
        IntSort(),
        {
            "nil": lambda: nil,
            "n": n,
        },
        {
            "list": list_unroll1,
            "lseg": lseg_unroll1,
        },
    )

    synthesizer.add_counterexample(counterexample, tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)))

    return synthesizer.synthesize()


def main():
    for formula in synthesize(term_depth=0, max_num_vars=3, max_num_hypotheses=2, allow_equality_in_conclusion=True):
        print(formula)


if __name__ == "__main__":
    main()
