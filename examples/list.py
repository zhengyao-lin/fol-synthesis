import itertools

from typing import Generator

from z3 import *
from synthesis import *


class HornClauseSynthesizer:
    def __init__(
        self,
        env: Z3Environment,
        language: Language,
        term_depth: int,
        max_num_vars: int,
        max_num_hypotheses: int,
        allow_equality_in_conclusion: bool = False,
    ):
        self.language = language
        self.counterexamples = []
        self.term_depth = term_depth
        self.max_num_vars = max_num_vars
        self.max_num_hypotheses = max_num_hypotheses
        self.previous_models = []

        self.env = env
        self.solver = Solver(ctx=env.context)
        self.hypotheses = tuple(
            AtomicFormulaVariable(self.env, language, term_depth, max_num_vars, allow_equality=False)
            for _ in range(max_num_hypotheses)
        )
        self.conclusion = AtomicFormulaVariable(self.env, language, term_depth, max_num_vars, allow_equality=allow_equality_in_conclusion)

        # add well-formedness constraints
        for hyp in self.hypotheses:
            self.solver.add(hyp.get_well_formedness_constraint())
        self.solver.add(self.conclusion.get_well_formedness_constraint())

    def add_example(self, example: Structure) -> None:
        assert example.universe is not None, "examples have to be concrete"

        for assignment in itertools.product(*([example.universe] * self.max_num_vars)):
            self.solver.add(Implies(
                And(*(hyp.eval(example, assignment) for hyp in self.hypotheses)),
                self.conclusion.eval(example, assignment),
            ))
    
    def add_counterexample(self, counterexample: Structure, assignment: Tuple[ArithRef, ...]) -> None:
        self.solver.add(Not(Implies(
            And(*(hyp.eval(counterexample, assignment) for hyp in self.hypotheses)),
            self.conclusion.eval(counterexample, assignment),
        )))
        self.counterexamples.append(counterexample)

    def get_counterexample(self) -> Structure:
        assert len(self.counterexamples)
        return self.counterexamples[0]

    def dismiss_previous_models(self) -> None:
        counterexample = self.get_counterexample()

        # require that any new formula is not implied by existing ones
        # even after permutation of variables
        assignment = tuple(FreshInt(ctx=self.env.context) for _ in range(self.max_num_vars))

        for permutation in itertools.permutations(assignment):
            previous_formulas = And(*(
                Implies(
                    And(*(
                        hyp.eval_z3_model(model, counterexample, permutation)
                        for hyp in self.hypotheses
                    )),
                    self.conclusion.eval_z3_model(model, counterexample, permutation),
                )
                for model in self.previous_models
            ))

            self.solver.add(Not(Implies(
                previous_formulas,
                Implies(
                    And(*(
                        hyp.eval(counterexample, assignment)
                        for hyp in self.hypotheses
                    )),
                    self.conclusion.eval(counterexample, assignment),
                ),
            )))

    def synthesize(self) -> Generator[str, None, None]:
        for num_hypotheses in range(self.max_num_hypotheses + 1):
            print(f"synthesizing formulas with {num_hypotheses} hypothesis(es)")
            while True:
                self.solver.push()

                self.dismiss_previous_models()

                # force the number of hypotheses
                for hyp in self.hypotheses[num_hypotheses:]:
                    self.solver.add(hyp.get_is_constant_constraint(True))

                if self.solver.check() != sat:
                    self.solver.pop()
                    break

                model = self.solver.model()
                self.solver.pop()

                self.previous_models.append(model)

                hypothesis_strings = tuple(hyp.unparse_z3_model(model) for hyp in self.hypotheses[:num_hypotheses])
                hypothesis_string = " /\\ ".join(hypothesis_strings)
                conclusion_string = self.conclusion.unparse_z3_model(model)

                yield f"{hypothesis_string} => {conclusion_string}"


def synthesize_in_list(*args, **kwargs) -> Generator[str, None, None]:
    env = Z3Environment(None)
    list_language = Language({ "nil": 0, "n": 1 }, { "list": 1, "lseg": 2 })
    synthesizer = HornClauseSynthesizer(env, list_language, *args, **kwargs)

    ##########################
    # load concrete examples #
    ##########################
    # list1_domain = { 0, 1, 2, 3 }
    # list1 = FiniteStructure.create(
    #     env,
    #     list_language,
    #     list1_domain,
    #     {
    #         "nil": 0,
    #         "n": {
    #             0: 0,
    #             1: 0,
    #             2: 1,
    #             3: 2,
    #         },
    #     },
    #     {
    #         "list": { 0, 1, 2, 3 },
    #         "lseg": { (x, y) for x in list1_domain for y in list1_domain if x >= y }
    #     },
    # )

    list2_domain = { 0, 1, 2, 3, 4, 5 }
    list2 = FiniteStructure.create(
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

    # synthesizer.add_example(list1)
    synthesizer.add_example(list2)

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
    for formula in synthesize_in_list(term_depth=0, max_num_vars=2, max_num_hypotheses=2, allow_equality_in_conclusion=True):
        print(formula)


if __name__ == "__main__":
    main()
