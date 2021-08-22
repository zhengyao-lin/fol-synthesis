from typing import Any, Tuple, Generator, List

from contextlib import contextmanager

from synthesis.smt import smt

from .base import *
from .templates import StructureTemplate


class CEGISynthesizer:
    """
    Synthesize formulas that are valid in some class of models
    but not always true in some other class
    """

    @contextmanager
    def solver_push(self, solver: smt.SMTSolver) -> Generator[None, None, None]:
        try:
            solver.push()
            yield
        finally:
            solver.pop()

    def synthesize_for_model_classes(
        self,
        templates: Tuple[Formula, ...],
        trivial_model: StructureTemplate,
        goal_model: StructureTemplate,
        *_: Any,
        solver_name: str = "z3",
    ) -> Generator[Formula, None, None]:
        """
        Given a class of models C_1 (described by <trivial_model>)
        and another class of models C_2 (described by <goal_model>)
        Synthesize all formula phi (using each template in <templates> in sequence)
        such that
          - exists M in C_1, not (M |= phi)
          - forall M in C_2, M |= phi

        If the second condition is not true, the counterexample model M is
        added back to the first round as an additional constraint

        e.g. to synthesize formulas true in all bounded finite LFP models but not in all FO model,
        we can take C_1 to be FOProvableStructure and C_2 to be FiniteLFPStructureTemplate

        e.g. to synthesize formulas true in a FO theory T but not in a FO subtheory T'
        we can take C_1 to be FOProvableStructure(T') and C_2 to be FOProvableStructure(T)
        """

        counterexamples: List[Structure] = []
        synthesized_formulas: List[Formula] = []
        
        with smt.Solver(name=solver_name) as gen_solver, \
             smt.Solver(name=solver_name) as check_solver: # to check that the synthesized formulas are valid

            gen_solver.add_assertion(trivial_model.get_constraint())
            check_solver.add_assertion(goal_model.get_constraint())

            for template in templates:
                print(f"### synthesizing formulas of the form {template}")

                with self.solver_push(gen_solver):
                    gen_solver.add_assertion(template.get_constraint())

                    # add all existing counterexamples
                    for counterexample in counterexamples:
                        gen_solver.add_assertion(template.quantify_all_free_variables().interpret(counterexample, {}))

                    # avoid duplicates for all existing formulas
                    for formula in synthesized_formulas:
                        gen_solver.add_assertion(formula.quantify_all_free_variables().interpret(trivial_model, {}))

                    # when negated, the (universally quantified) free variables
                    # become existentially quantified, we do skolemization here
                    free_vars = template.get_free_variables()
                    gen_skolem_constants = { # for the fo provable structure
                        v: trivial_model.interpret_sort(v.sort).get_fresh_constant(gen_solver, v.sort)
                        for v in free_vars
                    }
                    check_skolem_constants = { # for the counterexample
                        v: goal_model.interpret_sort(v.sort).get_fresh_constant(check_solver, v.sort)
                        for v in free_vars
                    }

                    # not valid in some trivial model
                    gen_solver.add_assertion(smt.Not(template.interpret(trivial_model, gen_skolem_constants)))

                    while gen_solver.solve():
                        candidate = template.get_from_smt_model(gen_solver.get_model())
                        print(candidate, "... ", end="", flush=True)

                        # check if the candidate is valid in all goal models
                        with self.solver_push(check_solver):
                            check_solver.add_assertion(smt.Not(candidate.interpret(goal_model, check_skolem_constants)))

                            if check_solver.solve():
                                # found counterexample
                                print("✘")
                                counterexample = goal_model.get_from_smt_model(check_solver.get_model())
                                counterexamples.append(counterexample)
                                gen_solver.add_assertion(template.quantify_all_free_variables().interpret(counterexample, {}))
                            else:
                                # no conuterexample found
                                print("✓")
                                yield candidate
                                synthesized_formulas.append(candidate)
                                gen_solver.add_assertion(candidate.quantify_all_free_variables().interpret(trivial_model, {}))
