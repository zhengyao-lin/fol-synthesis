from z3 import *
from synthesis import *


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language(
        { "nil": 0, "n": 1 },
        {
            "list": 1,
            "lseg": 2,
            # "len": 2,
        },
    )
    expanded_language = language.expand(
        {},
        { "in_lseg": 3 },
    )
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    synthesizer.dismiss_term(Application.parse("n(nil)"))

    ##########################
    # load concrete examples #
    ##########################

    # 2 -> 1 -> 0 = nil
    # 4 -> 3 -> 3
    # 5 -> 1
    # list(x) /\ list(y) /\ x != y => n(x) != n(y)
    # list1_domain = { 0, 1, 2, 3, 4 }
    # list1 = FiniteConcreteStructure.create(
    #     env,
    #     language,
    #     list1_domain,
    #     {
    #         "nil": 0,
    #         "n": {
    #             0: 0,
    #             1: 0,
    #             2: 1,
    #             3: 3,
    #             4: 3,
    #         },
    #     },
    #     {
    #         "list": { 0, 1, 2 },
    #         "lseg": { (x, y) for x in list1_domain for y in list1_domain if 2 >= x >= y }.union({
    #             (3, 3),
    #             (4, 3),
    #             (4, 4),
    #         }),
    #         "len": {
    #             (0, 0),
    #             (1, 1),
    #             (2, 2),
    #         }
    #     },
    # )

    # synthesizer.add_example(list1)

    apply_nil = lambda structure: structure.eval_function("nil", ())
    apply_n = lambda structure, x: structure.eval_function("n", (x,))
    apply_list = lambda structure, x: structure.eval_relation("list", (x,))
    apply_lseg = lambda structure, x, y: structure.eval_relation("lseg", (x, y))
    apply_in_lseg = lambda structure, x, y, z: structure.eval_relation("in_lseg", (x, y, z))

    in_lseg_defn = lambda structure, x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, apply_in_lseg(structure, x, apply_n(structure, y), z))
        )

    list_defn = lambda structure, x: Or(
        x == apply_nil(structure),
        And(
            Not(x == apply_nil(structure)),
            apply_list(structure, apply_n(structure, x)),
            Not(apply_in_lseg(structure, x, apply_n(structure, x), apply_nil(structure))),
        ),
    )

    lseg_defn = lambda structure, x, y: Or(
        x == y,
        And(
            Not(x == y),
            apply_lseg(structure, apply_n(structure, x), y),
            Not(apply_in_lseg(structure, x, apply_n(structure, x), y)),
        ),
    )

    syn_counterexample_unrolled = Structure(
        IntSort(),
        expanded_language,
        {
            "nil": (lambda nil: lambda: nil)(FreshInt()),
            "n": FreshFunction(IntSort(), IntSort()),
        },
        {
            "list": FreshFunction(IntSort(), BoolSort()),
            "lseg": FreshFunction(IntSort(), IntSort(), BoolSort()),
            "in_lseg": FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort()),
        },
    )

    for _ in range(2):
        syn_counterexample_unrolled = Structure(
            IntSort(),
            expanded_language,
            syn_counterexample_unrolled.function_interprets,
            {
                "lseg": (lambda structure: lambda x, y: lseg_defn(structure, x, y))(syn_counterexample_unrolled),
                "list": (lambda structure: lambda x: list_defn(structure, x))(syn_counterexample_unrolled),
                "in_lseg": (lambda structure: lambda x, y, z: in_lseg_defn(structure, x, y, z))(syn_counterexample_unrolled),
            },
        )

    synthesizer.set_synthesis_counterexample(
        syn_counterexample_unrolled,
        tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)),
    )

    ################# finite counterexample
    counterexample_size = 5

    ver_counterexample = FiniteSymbolicStructure.create(
        env,
        expanded_language,
        counterexample_size,
        function_overrides={},
        relation_overrides={},
    )

    ver_counterexample_unrolled = ver_counterexample
    for _ in range(counterexample_size + 1):
        ver_counterexample_unrolled = Structure(
            IntSort(),
            expanded_language,
            ver_counterexample_unrolled.function_interprets,
            {
                "lseg": (lambda structure: lambda x, y: lseg_defn(structure, x, y))(ver_counterexample_unrolled),
                "list": (lambda structure: lambda x: list_defn(structure, x))(ver_counterexample_unrolled),
                "in_lseg": (lambda structure: lambda x, y, z: in_lseg_defn(structure, x, y, z))(ver_counterexample_unrolled),
            },
        )

    for x, y, z in ver_counterexample.iterate_universe(3):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("in_lseg", (x, y, z)) == \
            in_lseg_defn(ver_counterexample_unrolled, x, y, z),
        )

    for x, y in ver_counterexample.iterate_universe(2):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("lseg", (x, y)) == \
            lseg_defn(ver_counterexample_unrolled, x, y),
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("list", (x,)) == \
            list_defn(ver_counterexample_unrolled, x),
        )

    synthesizer.set_verification_counterexample(ver_counterexample)

    return synthesizer.synthesize()


def main():
    for formula in synthesize(
        hypothesis_term_depth=0,
        conclusion_term_depth=0,
        max_num_vars=3,
        max_num_hypotheses=2,
        allow_equality_in_conclusion=True,
    ):
        print(formula)


if __name__ == "__main__":
    main()
