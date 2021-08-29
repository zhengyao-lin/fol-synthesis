from synthesis import *
from synthesis import modal


trivial_theory = Parser.parse_theory(r"""
theory REFLEXIVE
    sort W
    relation R: W W
    relation P: W
end
""")

reflexivity_theory = Parser.parse_theory(r"""
theory REFLEXIVE
    sort W
    relation R: W W
    relation P: W
    axiom forall x: W. R(x, x)
end
""")

transitive_theory = Parser.parse_theory(r"""
theory TRTANSITIVE
    sort W
    relation R: W W
    relation P: W
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(y, z) -> R(x, z)
end
""")

symmetric_theory = Parser.parse_theory(r"""
theory SYMMETRIC
    sort W
    relation R: W W
    relation P: W
    axiom forall x: W, y: W. R(x, y) -> R(y, x)
end
""")

euclidean_theory = Parser.parse_theory(r"""
theory EUCLIDEAN
    sort W
    relation R: W W
    relation P: W
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y)
end
""")

goal_theory = euclidean_theory

sort_world = trivial_theory.language.get_sort("W")
transition_relation = trivial_theory.language.get_relation_symbol("R")
p_relation = trivial_theory.language.get_relation_symbol("P")

atom_p = modal.Atom("p")

formula_template = modal.ModalFormulaTemplate((atom_p,), 3)

# modal.Implication(
#     modal.Modality(modal.Modality(atom_p)),
#     modal.Disjunction(
#         modal.Modality(atom_p),
#         atom_p,
#     ),
# )

trivial_model = FiniteFOModelTemplate(trivial_theory, { sort_world: 4 })
goal_model = FiniteFOModelTemplate(goal_theory, { sort_world: 4 })

true_formulas = []

with smt.Solver(name="z3") as solver1, \
     smt.Solver(name="z3") as solver2:
    solver1.add_assertion(formula_template.get_constraint())
    solver1.add_assertion(trivial_model.get_constraint())
    solver2.add_assertion(goal_model.get_constraint())

    # state that the formula should not hold on all frames
    solver1.add_assertion(smt.Not(formula_template.interpret_on_all_worlds(
        modal.FOStructureFrame(trivial_model, sort_world, transition_relation),
        {
            atom_p: lambda world: trivial_model.interpret_relation(p_relation, world),
        },
    )))

    while solver1.solve():
        candidate = formula_template.get_from_smt_model(solver1.get_model())
        print(candidate, end="", flush=True)

        solver2.push()

        # try to find a frame in which the candidate does not hold on all worlds
        solver2.add_assertion(smt.Not(candidate.interpret_on_all_worlds(
            modal.FOStructureFrame(goal_model, sort_world, transition_relation),
            {
                atom_p: lambda world: goal_model.interpret_relation(p_relation, world),
            },
        )))

        if solver2.solve():
            print(" ... ✘")
            # add the counterexample
            counterexample = goal_model.get_from_smt_model(solver2.get_model())
            solver1.add_assertion(formula_template.interpret_on_all_worlds(
                modal.FOStructureFrame(counterexample, sort_world, transition_relation),
                {
                    atom_p: lambda world: counterexample.interpret_relation(p_relation, world),
                },
            ))
        else:
            print(" ... ✓")
            true_formulas.append(candidate)
            # restrict trivial models to the ones where the candidate holds
            solver1.add_assertion(candidate.interpret_on_all_worlds(
                modal.FOStructureFrame(trivial_model, sort_world, transition_relation),
                {
                    atom_p: lambda world: trivial_model.interpret_relation(p_relation, world),
                },
            ))

        solver2.pop()

# check completeness
if len(true_formulas) != 0:
    axiom = true_formulas[-1]

    for formula in true_formulas[:-1]:
        axiom = modal.Conjunction(formula, axiom)

    print(f"is {axiom} complete", end="", flush=True)

    with smt.Solver(name="z3") as solver:
        model = FOModelTemplate(goal_theory)
        solver.add_assertion(model.get_constraint())

        solver.add_assertion(smt.Not(axiom.interpret_on_all_worlds(
            modal.FOStructureFrame(model, sort_world, transition_relation),
            {
                atom_p: lambda world: model.interpret_relation(p_relation, world),
            }
        )))

        if solver.solve():
            print(" ... ✘")
        else:
            print(" ... ✓")
