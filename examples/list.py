import itertools

from z3 import *
from synthesis import *

env = Z3Environment(None)

list_language = Language({ "nil": 0, "n": 1 }, { "list": 1, "lseg": 2 })

TERM_DEPTH = 0
NUM_VARS = 3
NUM_HYPS = 2

hypotheses = tuple(AtomicFormulaVariable(env, list_language, TERM_DEPTH, NUM_VARS) for _ in range(NUM_HYPS))
conclusion = AtomicFormulaVariable(env, list_language, TERM_DEPTH, NUM_VARS)


def eval_hypotheses(structure, assignment):
    return And(*(hyp.eval(structure, assignment) for hyp in hypotheses))


def satisfies(solver, structure, domain):
    for assignment in itertools.product(*([domain] * NUM_VARS)):
        solver.add(Implies(
            eval_hypotheses(structure, assignment),
            conclusion.eval(structure, assignment),
        ))


def satisfies_examples(solver):
    list1_domain = { 0, 1, 2, 3 }
    list1 = Structure.from_finite_int(
        env,
        list_language,
        list1_domain,
        {
            "nil": 0,
            "n": {
                0: 0,
                1: 0,
                2: 1,
                3: 2,
            },
        },
        {
            "list": { 0, 1, 2, 3 },
            "lseg": { (x, y) for x in list1_domain for y in list1_domain if x >= y }
        },
    )

    list2_domain = { 0, 1, 2, 3, 4, 5 }
    list2 = Structure.from_finite_int(
        env,
        list_language,
        list2_domain,
        {
            "nil": 0,
            "n": {
                0: 0,
                1: 0,
                2: 1,
                3: 2,
                4: 4,
                5: 4,
            },
        },
        {
            "list": { 0, 1, 2, 3 },
            "lseg": { (x, y) for x in list2_domain for y in list2_domain if 3 >= x >= y }.union({
                (4, 4),
                (5, 4),
                (5, 5),
            })
        },
    )

    # the formula satisfies the examples
    satisfies(solver, list1, list1_domain)
    satisfies(solver, list2, list2_domain)


def nontrivial_implication(solver):
    # arbitrary combination of n hypotheses, where 0 <= n < len(hypotheses)
    # should not imply the conclusion
    for n in range(0, len(hypotheses)):
        for combination in itertools.product(*([hypotheses] * n)):
            free_vars = tuple(FreshInt() for _ in range(NUM_VARS))
            solver.add(Not(Implies(
                And(*(hyp.eval(counterexample, free_vars) for hyp in combination)),
                conclusion.eval(counterexample, free_vars),
            )))

    # the formulas are not trivially true
    for hyp in hypotheses:
        solver.add(Not(hyp.eval(counterexample, tuple(FreshInt() for _ in range(NUM_VARS)))))

    solver.add(Not(conclusion.eval(counterexample, tuple(FreshInt() for _ in range(NUM_VARS)))))


########################
# encoding constraints #
########################

solver = Solver()

for hyp in hypotheses:
    solver.add(hyp.get_well_formedness_constraint())
solver.add(conclusion.get_well_formedness_constraint())

satisfies_examples(solver)

# the formula should have a counterexample in FO-semantcs
nil_uninterp = 0
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
    x == nil_uninterp,
    And(
        Not(x == nil_uninterp),
        list_uninterp(n_uninterp(x)),
        Not(in_lseg_unfold1(x, n_uninterp(x), nil_uninterp)),
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
        "nil": lambda: nil_uninterp,
        "n": n_uninterp,
    },
    {
        "list": list_unfold1,
        "lseg": lseg_unfold1,
    },
)

counterexample_assignment = tuple(FreshInt() for _ in range(NUM_VARS))

solver.add(Not(Implies(
    eval_hypotheses(counterexample, counterexample_assignment),
    conclusion.eval(counterexample, counterexample_assignment),
)))

# some lemmas to rule out trivial formulas
v = FreshInt()
solver.add(ForAll([v], Implies(lseg_unfold1(v, nil_uninterp), list_unfold1(v))))
solver.add(ForAll([v], Implies(list_unfold1(v), lseg_unfold1(v, nil_uninterp))))
solver.add(ForAll([v], Implies(lseg_unfold1(nil_uninterp, v), v == nil_uninterp)))

nontrivial_implication(solver)

print("generating models")

# print all possible models
while True:
    if solver.check() == sat:
        model = solver.model()

        hyp_strings = tuple(hyp.unparse_z3_model(model) for hyp in hypotheses)

        print(
            " /\\ ".join(hyp_strings),
            "=>",
            conclusion.unparse_z3_model(model),
        )

        solver.add(Or(
            *(hyp.dismiss_z3_model(model) for hyp in hypotheses),
            conclusion.dismiss_z3_model(model),
        ))

        # require that any new formula is not implied by existing ones
        # even after permutation of variables
        assignment = tuple(FreshInt() for _ in range(NUM_VARS))

        for permutation in itertools.permutations(assignment):
            solver.add(Not(
                Implies(
                    Implies(
                        eval_hypotheses(counterexample, permutation),
                        conclusion.eval(counterexample, permutation),
                    ), Implies(
                        And(*(
                            hyp.eval_z3_model(model, counterexample, assignment)
                            for hyp in hypotheses
                        )),
                        conclusion.eval_z3_model(model, counterexample, assignment),
                    )
                ),
            ))
    else:
        print("unsat")
        break
