from z3 import *
from synthesis import *


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language(
        { "nil": 0, "n": 1, "p": 1 },
        {
            "list": 1,
            "dlist": 1,
            "dlseg": 2,
        },
    )
    expanded_language = language.expand(
        {},
        {
            "in_lsegf": 3,
            "in_lsegb": 3,
        },
    )
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    # list1_domain = { 0, 1, 2, 3, 4 }
    # list1 = FiniteConcreteStructure.create(
    #     env,
    #     language,
    #     list1_domain,
    #     {
    #         "nil": 0,
    #         "next": {
    #             0: 0,
    #             1: 0,
    #             2: 1,
    #             3: 3,
    #             4: 3,
    #         },
    #         "prev": {
    #             0: 0,
    #             1: 2,
    #             2: 2,
    #             3: 4,
    #             4: 4,
    #         }
    #     },
    #     {
    #         "list": { 0, 1, 2 },
    #         "dlist": { 0, 1 },
    #     },
    # )

    # synthesizer.add_example(list1)

    ################################
    # construct the counterexample #
    ################################

    apply_nil = lambda structure: structure.eval_function("nil", ())
    apply_n = lambda structure, x: structure.eval_function("n", (x,))
    apply_p = lambda structure, x: structure.eval_function("p", (x,))
    apply_list = lambda structure, x: structure.eval_relation("list", (x,))
    apply_dlist = lambda structure, x: structure.eval_relation("dlist", (x,))
    apply_dlseg = lambda structure, x, y: structure.eval_relation("dlseg", (x, y))
    apply_in_lsegf = lambda structure, x, y, z: structure.eval_relation("in_lsegf", (x, y, z))
    apply_in_lsegb = lambda structure, x, y, z: structure.eval_relation("in_lsegb", (x, y, z))
    
    in_lsegf_defn = lambda structure, x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, apply_in_lsegf(structure, x, apply_n(structure, y), z))
        )

    in_lsegb_defn = lambda structure, x, y, z: \
        If(
            y == z,
            False,
            Or(x == y, apply_in_lsegb(structure, x, apply_p(structure, y), z))
        )

    list_defn = lambda structure, x: Or(
        x == apply_nil(structure),
        And(
            Not(x == apply_nil(structure)),
            apply_list(structure, apply_n(structure, x)),
            Not(apply_in_lsegf(structure, x, apply_n(structure, x), apply_nil(structure))),
        ),
    )

    dlist_defn = lambda structure, x: Or(
        Or(x == apply_nil(structure), apply_n(structure, x) == apply_nil(structure)),
        And(
            Not(x == apply_nil(structure)), Not(apply_n(structure, x) == apply_nil(structure)),
            apply_p(structure, apply_n(structure, x)) == x,
            apply_dlist(structure, apply_n(structure, x)),
            Not(apply_in_lsegf(structure, x, apply_n(structure, x), apply_nil(structure))),
            Not(apply_in_lsegb(structure, x, apply_p(structure, x), apply_nil(structure))),
        ),
    )

    dlseg_defn = lambda structure, x, y: Or(
        z3.And(x == y),
        z3.And(
            z3.Not(x == y),
            apply_p(structure, apply_n(structure, x)) == x,
            apply_dlseg(structure, apply_n(structure, x), y),
            z3.Not(apply_in_lsegf(structure, x, apply_n(structure, x), y)),
            z3.Not(apply_in_lsegb(structure, y, x, apply_p(structure, y))),
            z3.Not(apply_in_lsegb(structure, x, apply_nil(structure), apply_p(structure, x))),
        ),
    )

    syn_counterexample_unrolled = Structure(
        IntSort(),
        expanded_language,
        {
            "nil": (lambda nil: lambda: nil)(FreshInt()),
            "n": FreshFunction(IntSort(), IntSort()),
            "p": FreshFunction(IntSort(), IntSort()),
        },
        {
            "list": FreshFunction(IntSort(), BoolSort()),
            "dlist": FreshFunction(IntSort(), BoolSort()),
            "dlseg": FreshFunction(IntSort(), IntSort(), BoolSort()),
            "in_lsegf": FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort()),
            "in_lsegb": FreshFunction(IntSort(), IntSort(), IntSort(), BoolSort()),
        },
    )

    for _ in range(2):
        syn_counterexample_unrolled = Structure(
            IntSort(),
            expanded_language,
            syn_counterexample_unrolled.function_interprets,
            {
                "list": (lambda structure: lambda x: list_defn(structure, x))(syn_counterexample_unrolled),
                "dlist": (lambda structure: lambda x: dlist_defn(structure, x))(syn_counterexample_unrolled),
                "dlseg": (lambda structure: lambda x, y: dlseg_defn(structure, x, y))(syn_counterexample_unrolled),
                "in_lsegf": (lambda structure: lambda x, y, z: in_lsegf_defn(structure, x, y, z))(syn_counterexample_unrolled),
                "in_lsegb": (lambda structure: lambda x, y, z: in_lsegb_defn(structure, x, y, z))(syn_counterexample_unrolled),
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
                "list": (lambda structure: lambda x: list_defn(structure, x))(ver_counterexample_unrolled),
                "dlist": (lambda structure: lambda x: dlist_defn(structure, x))(ver_counterexample_unrolled),
                "dlseg": (lambda structure: lambda x, y: dlseg_defn(structure, x, y))(ver_counterexample_unrolled),
                "in_lsegf": (lambda structure: lambda x, y, z: in_lsegf_defn(structure, x, y, z))(ver_counterexample_unrolled),
                "in_lsegb": (lambda structure: lambda x, y, z: in_lsegb_defn(structure, x, y, z))(ver_counterexample_unrolled),
            },
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("list", (x,)) == \
            list_defn(ver_counterexample_unrolled, x),
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("dlist", (x,)) == \
            dlist_defn(ver_counterexample_unrolled, x),
        )

    for x, y in ver_counterexample.iterate_universe(2):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("dlseg", (x, y)) == \
            dlseg_defn(ver_counterexample_unrolled, x, y),
        )

    for x, y, z in ver_counterexample.iterate_universe(3):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("in_lsegf", (x, y, z)) == \
            in_lsegf_defn(ver_counterexample_unrolled, x, y, z),
        )

    for x, y, z in ver_counterexample.iterate_universe(3):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("in_lsegb", (x, y, z)) == \
            in_lsegb_defn(ver_counterexample_unrolled, x, y, z),
        )

    synthesizer.set_verification_counterexample(ver_counterexample)

    return synthesizer.synthesize()


def main():
    for formula in synthesize(
        hypothesis_term_depth=0,
        conclusion_term_depth=0,
        max_num_vars=3,
        max_num_hypotheses=2,
        allow_equality_in_conclusion=False,
    ):
        print(formula)


if __name__ == "__main__":
    main()
