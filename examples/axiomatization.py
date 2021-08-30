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
transition_symbol = trivial_theory.language.get_relation_symbol("R")
p_symbol = trivial_theory.language.get_relation_symbol("P")

atom_p = modal.Atom("p")

formula_template = modal.ModalFormulaTemplate((atom_p,), 3)

# complete axiom for symmetric frames
# formula_template = modal.Implication(
#     atom_p,
#     modal.Modality(modal.Negation(modal.Modality(modal.Negation(atom_p)))),
# )

# complete axiom for euclidean frames
# formula_template = modal.Implication(
#     modal.Negation(modal.Modality(modal.Negation(atom_p))),
#     modal.Modality(modal.Negation(modal.Modality(modal.Negation(atom_p)))),
# )

# true in symmetric frames but not complete
# formula_template = modal.Implication(
#     modal.Modality(modal.Modality(atom_p)),
#     modal.Disjunction(
#         modal.Modality(atom_p),
#         atom_p,
#     ),
# )

model_size_bound = 4

# trivial_model = FOModelTemplate(trivial_theory)
trivial_model = FiniteFOModelTemplate(trivial_theory, { sort_world: model_size_bound })
goal_model = FiniteFOModelTemplate(goal_theory, { sort_world: model_size_bound })

true_formulas = []

with smt.Solver(name="z3") as solver1, \
     smt.Solver(name="z3") as solver2:
    solver1.add_assertion(formula_template.get_constraint())
    solver1.add_assertion(trivial_model.get_constraint())
    solver2.add_assertion(goal_model.get_constraint())

    # state that the formula should not hold on all frames
    solver1.add_assertion(smt.Not(formula_template.interpret_on_all_worlds(
        modal.FOStructureFrame(trivial_model, sort_world, transition_symbol),
        {
            atom_p: lambda world: trivial_model.interpret_relation(p_symbol, world),
        },
    )))

    while solver1.solve():
        candidate = formula_template.get_from_smt_model(solver1.get_model())
        print(candidate, end="", flush=True)

        solver2.push()

        # try to find a frame in which the candidate does not hold on all worlds
        solver2.add_assertion(smt.Not(candidate.interpret_on_all_worlds(
            modal.FOStructureFrame(goal_model, sort_world, transition_symbol),
            {
                atom_p: lambda world: goal_model.interpret_relation(p_symbol, world),
            },
        )))

        if solver2.solve():
            print(" ... ✘")
            # add the counterexample
            counterexample = goal_model.get_from_smt_model(solver2.get_model())
            solver1.add_assertion(formula_template.interpret_on_all_worlds(
                modal.FOStructureFrame(counterexample, sort_world, transition_symbol),
                {
                    atom_p: lambda world: counterexample.interpret_relation(p_symbol, world),
                },
            ))
        else:
            print(" ... ✓")
            true_formulas.append(candidate)
            # restrict trivial models to the ones where the candidate holds
            # TODO: here we preferably want to quantify over all P

            carrier = trivial_model.interpret_sort(sort_world)
            assert isinstance(carrier, FiniteCarrierSet)
            
            p_values = tuple(smt.FreshSymbol(smt.BOOL) for _ in range(model_size_bound))
            p_relation = (lambda p_values: lambda world: smt.Or(
                smt.And(
                    smt.Equals(world, carrier.domain[i]),
                    p_values[i],
                )
                for i in range(model_size_bound)
            ))(p_values)

            solver1.add_assertion(smt.ForAll(p_values, candidate.interpret_on_all_worlds(
                modal.FOStructureFrame(trivial_model, sort_world, transition_symbol),
                {
                    atom_p: p_relation,
                },
            )))

        solver2.pop()

# check completeness of the axioms on a set of finite structures with bounded size
if len(true_formulas) != 0:
    axiomatization = true_formulas[-1]
    for formula in true_formulas[:-1]:
        axiomatization = modal.Conjunction(formula, axiomatization)

    print(f"is {axiomatization} complete", end="", flush=True)

    complement_axiom: Formula = Falsum()

    for sentence in goal_theory.sentences:
        if isinstance(sentence, Axiom):
            complement_axiom = Disjunction(complement_axiom, Negation(sentence.formula))

    complement_theory = trivial_theory.extend_axioms((complement_axiom,))

    with smt.Solver(name="z3") as solver:
        # check that the axiomatization does not hold on a non-model of the goal_theory
        complement_model = FiniteFOModelTemplate(complement_theory, { sort_world: model_size_bound })
        solver.add_assertion(complement_model.get_constraint())

        carrier = complement_model.interpret_sort(sort_world)
        assert isinstance(carrier, FiniteCarrierSet)
        
        p_values = tuple(smt.FreshSymbol(smt.BOOL) for _ in range(model_size_bound))
        p_relation = lambda world: smt.Or(
            smt.And(
                smt.Equals(world, carrier.domain[i]),
                p_values[i],
            )
            for i in range(model_size_bound)
        )

        # need to quantify over all relations P
        solver.add_assertion(smt.ForAll(p_values, axiomatization.interpret_on_all_worlds(
            modal.FOStructureFrame(complement_model, sort_world, transition_symbol),
            {
                atom_p: p_relation,
            }
        )))

        if solver.solve():
            print(" ... ✘")
            # counterexample = complement_model.get_from_smt_model(solver.get_model())
            # print(counterexample.carriers[sort_world])
            # print(counterexample.interpret_relation(transition_symbol, smt.Int(0), smt.Int(0)))
            # print(counterexample.interpret_relation(p_symbol, smt.Int(0)))
        else:
            print(" ... ✓")
