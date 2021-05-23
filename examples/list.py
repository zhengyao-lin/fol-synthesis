from z3 import *
from synthesis import *


def synthesize_in_list(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    list_language = Language({ "nil": 0, "n": 1 }, { "list": 1, "lseg": 2 })
    synthesizer = HornClauseSynthesizer(env, list_language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    list1_domain = { 0, 1, 2, 3, 4 }
    list1 = FiniteStructure.create(
        env,
        list_language,
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
    n_uninterp = FreshFunction(IntSort(), IntSort())
    list_uninterp = FreshFunction(IntSort(), BoolSort())
    lseg_uninterp = FreshFunction(IntSort(), IntSort(), BoolSort())
    in_lseg_uninterp = FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort())

    in_lseg_unfold1 = lambda x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, in_lseg_uninterp(x, n_uninterp(y), z))
        )

    list_unfold1 = lambda x: Or(
        x == nil,
        And(
            Not(x == nil),
            list_uninterp(n_uninterp(x)),
            Not(in_lseg_unfold1(x, n_uninterp(x), nil)),
        ),
    )

    lseg_unfold1 = lambda x, y: Or(
        x == y,
        And(
            Not(x == y),
            lseg_uninterp(n_uninterp(x), y),
            Not(in_lseg_unfold1(x, n_uninterp(x), y)),
        ),
    )

    counterexample = Structure(
        IntSort(),
        {
            "nil": lambda: nil,
            "n": n_uninterp,
        },
        {
            "list": list_unfold1,
            "lseg": lseg_unfold1,
        },
    )

    synthesizer.add_counterexample(counterexample, tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)))

    return synthesizer.synthesize()


def main():
    for formula in synthesize_in_list(term_depth=0, max_num_vars=3, max_num_hypotheses=2, allow_equality_in_conclusion=True):
        print(formula)


if __name__ == "__main__":
    main()
