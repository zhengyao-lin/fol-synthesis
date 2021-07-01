from z3 import *
from synthesis import *

set_param("parallel.enable", True)
set_param("parallel.threads.max", 4)


def synthesize(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    language = Language(
        { "nil": 0, "left": 1, "right": 1, "key": 1, "v": 0 },
        {
            "btree": 1,
            "bst": 1,
            "le": 2,
            "ne": 2,
            "leftmost": 2,
        })
    expanded_language = language.expand(
        {},
        { "in_bst": 2 },
    )
    synthesizer = HornClauseSynthesizer(env, language, *args, **kwargs)

    # extra constraints on the well-formedness of formulas/terms
    synthesizer.dismiss_term(Application.parse("left(nil)"))
    synthesizer.dismiss_term(Application.parse("right(nil)"))
    synthesizer.dismiss_term(Application.parse("key(nil)"))
    synthesizer.dismiss_term(Application.parse("key(v)"))
    synthesizer.dismiss_term(Application.parse("left(v)"))
    synthesizer.dismiss_term(Application.parse("right(v)"))
    synthesizer.dismiss_term(Application.parse("left(key(<any>))"))
    synthesizer.dismiss_term(Application.parse("right(key(<any>))"))

    synthesizer.dismiss_atomic_formula(Application.parse("bst(key(<any>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("btree(key(<any>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("bst(v)"))
    synthesizer.dismiss_atomic_formula(Application.parse("btree(v)"))

    synthesizer.dismiss_atomic_formula(Application.parse("ne(v, <variable>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(<variable>, v)"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(key(<any>), <variable>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(<variable>, key(<any>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(v, left(<variable>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(left(<variable>), v)"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(key(<any>), left(<variable>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(left(<variable>), key(<any>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(v, right(<variable>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(right(<variable>), v)"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(key(<any>), right(<variable>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("ne(right(<variable>), key(<any>))"))

    synthesizer.dismiss_atomic_formula(Application.parse("le(<variable>, <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(<any>, <variable>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(nil, <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(<any>, nil)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(left(<any>), <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(<any>, left(<any>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(right(<any>), <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("le(<any>, right(<any>))"))

    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(<any>, nil)"))
    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(nil, <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(v, <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(key(<any>), <any>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(<any>, <variable>)"))
    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(<any>, right(<any>))"))
    synthesizer.dismiss_atomic_formula(Application.parse("leftmost(<any>, left(<any>))"))

    # check why a specific formula is rejected
    # synthesizer.add_synthesis_constraint(z3.Not(z3.Or(
    #     synthesizer.hypotheses[0].dismiss_application(Application.parse("ne(<variable>, nil)")),
    #     synthesizer.hypotheses[1].dismiss_application(Application.parse("bst(<variable>)")),
    #     synthesizer.hypotheses[2].dismiss_application(Application.parse("leftmost(<variable>, v)")),
    #     synthesizer.conclusion.dismiss_application(Application.parse("le(v, key(<variable>))")),
    # )))

    v = z3.FreshInt()

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
        x == nil(structure),
        z3.And(left(structure, x) == nil(structure), right(structure, x) == nil(structure)),
        z3.And(
            btree(structure, left(structure, x)),
            btree(structure, right(structure, x)),
            z3.Not(in_bst(structure, x, left(structure, x))),
            z3.Not(in_bst(structure, x, right(structure, x))),
        ),
    )

    bst_defn = lambda structure, x: z3.Or(
        x == nil(structure),
        z3.And(left(structure, x) == nil(structure), right(structure, x) == nil(structure)),
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
        # z3.And(x == nil(structure), key(structure, nil(structure)) == y),
        z3.And(left(structure, x) == nil(structure), key(structure, x) == y),
        z3.And(z3.Not(left(structure, x) == nil(structure)), leftmost(structure, left(structure, x), y))
    )

    ################################
    # construct the counterexample #
    ################################
    syn_counterexample_unrolled = Structure(
        IntSort(),
        expanded_language,
        {
            "nil": (lambda nil: lambda: nil)(FreshInt()),
            "left": FreshFunction(IntSort(), IntSort()),
            "right": FreshFunction(IntSort(), IntSort()),
            "key": FreshFunction(IntSort(), IntSort()),
            "v": lambda: v,
        },
        {
            "in_bst": FreshFunction(IntSort(), IntSort(), BoolSort()),
            "btree": FreshFunction(IntSort(), BoolSort()),
            "bst": FreshFunction(IntSort(), BoolSort()),
            "leftmost": FreshFunction(IntSort(), IntSort(), BoolSort()),
            "le": lambda x, y: x <= y,
            "ne": lambda x, y: z3.Not(x == y),
        },
    )

    for _ in range(2):
        syn_counterexample_unrolled = Structure(
            IntSort(),
            expanded_language,
            syn_counterexample_unrolled.function_interprets,
            {
                "in_bst": (lambda structure: lambda x, y: in_bst_defn(structure, x, y))(syn_counterexample_unrolled),
                "btree": (lambda structure: lambda x: btree_defn(structure, x))(syn_counterexample_unrolled),
                "bst": (lambda structure: lambda x: bst_defn(structure, x))(syn_counterexample_unrolled),
                "leftmost": (lambda structure: lambda x, y: leftmost_defn(structure, x, y))(syn_counterexample_unrolled),
                "le": lambda x, y: x <= y,
                "ne": lambda x, y: z3.Not(x == y),
            },
        )

    synthesizer.set_synthesis_counterexample(
        syn_counterexample_unrolled,
        tuple(FreshInt(ctx=env.context) for _ in range(synthesizer.max_num_vars)),
    )

    counterexample_size = 3

    ver_counterexample = FiniteSymbolicStructure.create(
        env,
        expanded_language,
        counterexample_size,
        function_overrides={
            "key": FreshFunction(IntSort(), IntSort()),
            "v": lambda: v,
        },
        relation_overrides={
            "le": lambda x, y: x <= y,
            "ne": lambda x, y: z3.Not(x == y),
        },
    )

    ver_counterexample_unrolled = ver_counterexample
    for _ in range(counterexample_size + 1):
        ver_counterexample_unrolled = Structure(
            IntSort(),
            expanded_language,
            ver_counterexample_unrolled.function_interprets,
            {
                "in_bst": (lambda structure: lambda x, y: in_bst_defn(structure, x, y))(ver_counterexample_unrolled),
                "btree": (lambda structure: lambda x: btree_defn(structure, x))(ver_counterexample_unrolled),
                "bst": (lambda structure: lambda x: bst_defn(structure, x))(ver_counterexample_unrolled),
                "leftmost": (lambda structure: lambda x, y: leftmost_defn(structure, x, y))(ver_counterexample_unrolled),
                "le": lambda x, y: x <= y,
                "ne": lambda x, y: z3.Not(x == y),
            },
        )

    for x, y in ver_counterexample.iterate_universe(2):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("in_bst", (x, y)) == \
            in_bst_defn(ver_counterexample_unrolled, x, y),
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("btree", (x,)) == \
            btree_defn(ver_counterexample_unrolled, x),
        )

    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(
            ver_counterexample.eval_relation("bst", (x,)) == \
            bst_defn(ver_counterexample_unrolled, x),
        )

    y = z3.FreshInt()
    for x, in ver_counterexample.iterate_universe(1):
        synthesizer.add_verification_constraint(ForAll(
            [y],
            ver_counterexample.eval_relation("leftmost", (x, y)) == \
            leftmost_defn(ver_counterexample_unrolled, x, y),
        ))

    synthesizer.set_verification_counterexample(ver_counterexample)

    return synthesizer.synthesize()


def main():
    for formula in synthesize(
        hypothesis_term_depth=0,
        conclusion_term_depth=1,
        max_num_vars=1,
        min_num_hypotheses=0,
        max_num_hypotheses=3,
        allow_equality_in_conclusion=False,
    ):
        print(formula)


if __name__ == "__main__":
    main()
