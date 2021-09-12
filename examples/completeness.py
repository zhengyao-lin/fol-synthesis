from synthesis import *
from synthesis import modal


def count_modality(formula: modal.Formula) -> int:
    if isinstance(formula, modal.Verum) or \
       isinstance(formula, modal.Falsum) or \
       isinstance(formula, modal.Atom):
        return 0

    if isinstance(formula, modal.Negation):
        return count_modality(formula.formula)

    if isinstance(formula, modal.Conjunction) or \
       isinstance(formula, modal.Disjunction) or \
       isinstance(formula, modal.Implication):
        return count_modality(formula.left) + count_modality(formula.right)

    if isinstance(formula, modal.Equivalence):
        return 2 * (count_modality(formula.left) + count_modality(formula.right))

    if isinstance(formula, modal.Modality) or \
       isinstance(formula, modal.Diamond):
        return 1 + count_modality(formula.formula)

    assert False, f"unsupported modal formula {formula}"


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

rst_theory = Parser.parse_theory(r"""
theory RST
    sort W
    relation R: W W
    relation P: W
    axiom forall x: W, y: W, z: W. R(x, x) /\ (R(x, y) -> R(y, x)) /\ (R(x, y) /\ R(y, z) -> R(x, z))
end
""")

goal_theory = transitive_theory # euclidean_theory

sort_world = trivial_theory.language.get_sort("W")
transition_symbol = trivial_theory.language.get_relation_symbol("R")
p_symbol = trivial_theory.language.get_relation_symbol("P")

atom_p = modal.Atom("p")

formula_templates = (
    modal.ModalFormulaTemplate((atom_p,), 2),
    modal.ModalFormulaTemplate((atom_p,), 3),
    # modal.ModalFormulaTemplate((atom_p,), 4),
)

# formula_template = modal.ModalFormulaTemplate((atom_p,), 3)

# true in symmetric frames but not complete
# formula_templates = modal.Implication(
#     modal.Modality(modal.Modality(atom_p)),
#     modal.Disjunction(
#         modal.Modality(atom_p),
#         atom_p,
#     ),
# ),

# complete axiom for symmetric frames
# formula_templates = modal.Implication(
#     atom_p,
#     modal.Modality(modal.Diamond(atom_p)),
# ),

# complete axiom for euclidean frames
# formula_templates = modal.Implication(
#     modal.Diamond(atom_p),
#     modal.Modality(modal.Diamond(atom_p)),
# ),

# complete axiom for transitive frames
# formula_templates = modal.Implication(
#     modal.Modality(atom_p),
#     modal.Modality(modal.Modality(atom_p)),
# ),

model_size_bound = 4

# trivial_model = FOModelTemplate(trivial_theory)
trivial_model = FiniteFOModelTemplate(trivial_theory, { sort_world: model_size_bound })
goal_model = FiniteFOModelTemplate(goal_theory, { sort_world: model_size_bound })

true_formulas: List[modal.Formula] = []
counterexapmles: List[Structure] = []


def add_counterexample(solver: smt.SMTSolver, template: modal.Formula, counterexample: Structure) -> None:
    solver.add_assertion(template.interpret_on_all_worlds(
        modal.FOStructureFrame(counterexample, sort_world, transition_symbol),
        {
            atom_p: lambda world: counterexample.interpret_relation(p_symbol, world),
        },
    ))


def add_true_formula(solver: smt.SMTSolver, trivial_model: FiniteFOModelTemplate, formula: modal.Formula) -> None:
    # restrict trivial models to the ones where the formula holds
    p_relation, p_values = trivial_model.get_free_finite_relation((sort_world,))
    solver.add_assertion(smt.ForAll(p_values, formula.interpret_on_all_worlds(
        modal.FOStructureFrame(trivial_model, sort_world, transition_symbol),
        {
            atom_p: p_relation,
        },
    )))


with smt.Solver(name="z3") as solver1, \
     smt.Solver(name="z3") as solver2:

    solver1.add_assertion(trivial_model.get_constraint())
    solver2.add_assertion(goal_model.get_constraint())
    
    for formula_template in formula_templates:
        with smt.push_solver(solver1):
            # add all counterexamples and true formulas
            for counterexample in counterexapmles:
                add_counterexample(solver1, formula_template, counterexample)
            
            for formula in true_formulas:
                add_true_formula(solver1, trivial_model, formula)

            solver1.add_assertion(formula_template.get_constraint())

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
                    counterexapmles.append(counterexample)

                    add_counterexample(solver1, formula_template, counterexample)
                else:
                    print(" ... ✓")
                    true_formulas.append(candidate)
                    add_true_formula(solver1, trivial_model, candidate)

                solver2.pop()

# check completeness of the axioms on a set of finite structures with bounded size
if len(true_formulas) != 0:
    axiomatization = true_formulas[-1]
    for formula in true_formulas[:-1]:
        axiomatization = modal.Conjunction(formula, axiomatization)

    complement_axiom: Formula = Falsum()

    for sentence in goal_theory.sentences:
        if isinstance(sentence, Axiom):
            complement_axiom = Disjunction(complement_axiom, Negation(sentence.formula))

    complement_theory = trivial_theory.extend_axioms((complement_axiom,))

    with smt.Solver(name="z3") as solver:
        # check that the axiomatization does not hold on a non-model of the goal_theory
        complement_model = FOModelTemplate(complement_theory, smt.INT)
        solver.add_assertion(complement_model.get_constraint())

        # carrier_world = complement_model.interpret_sort(sort_world)

        # finite_subframe_tree_arity = 1
        # finite_subframe_tree_depth = 1

        # p_assignments = [
        #     smt.FreshSymbol(smt.BOOL),
        # ]
        # other_p_assignment = smt.FreshSymbol(smt.BOOL)
        # subframe = [
        #     (smt.FreshSymbol(carrier_world.get_smt_sort()),),
        # ]

        # shape_constraint = smt.TRUE()

        # for depth in range(finite_subframe_tree_depth):
        #     last_level = subframe[-1]
        #     level = []

        #     for parent_node in last_level:
        #         var = smt.FreshSymbol(carrier_world.get_smt_sort())
        #         no_successor_constraint = smt.Not(carrier_world.existentially_quantify(
        #             var,
        #             complement_model.interpret_relation(transition_symbol, parent_node, var),
        #         ))
        #         connectivity_constraint = smt.TRUE()

        #         for i in range(finite_subframe_tree_arity):
        #             node = smt.FreshSymbol(carrier_world.get_smt_sort())
        #             p_assignments.append(smt.FreshSymbol(smt.BOOL))
        #             level.append(node)

        #             connectivity_constraint = smt.And(
        #                 connectivity_constraint,
        #                 complement_model.interpret_relation(transition_symbol, parent_node, node),
        #             )

        #         shape_constraint = smt.And(
        #             shape_constraint,
        #             smt.Or(
        #                 no_successor_constraint,
        #                 connectivity_constraint,
        #             ),
        #         )

        #     subframe.append(tuple(level))
        
        # flatten_subframe = sum(subframe, ())

        # consistency_constraint = smt.TRUE()

        # # for the same node, the assignment should be the same
        # for i, node in enumerate(flatten_subframe):
        #     for j in range(i):
        #         consistency_constraint = smt.And(
        #             consistency_constraint,
        #             smt.Implies(
        #                 smt.Equals(flatten_subframe[i], flatten_subframe[j]),
        #                 smt.Iff(p_assignments[i], p_assignments[j]),
        #             )
        #         )

        # p_relation = lambda world: smt.Or(
        #     smt.Or(
        #         smt.And(
        #             smt.Equals(world, node),
        #             p_assignments[i],
        #         )
        #         for i, node in enumerate(flatten_subframe)
        #     ),
        #     smt.Or(
        #         smt.And(
        #             smt.And(
        #                 smt.Not(smt.Equals(world, node))
        #                 for node in flatten_subframe
        #             ),
        #             other_p_assignment,
        #         ),
        #     )
        # )

        # # the modal axiom is valid
        # valid_constraint = smt.ForAll(p_assignments + [other_p_assignment],
        #     smt.Implies(
        #         smt.And(
        #             shape_constraint,
        #             consistency_constraint,
        #         ),
        #         axiomatization.interpret(
        #             modal.FOStructureFrame(complement_model, sort_world, transition_symbol),
        #             {
        #                 atom_p: p_relation,
        #             },
        #             flatten_subframe[0],
        #         ),
        #     ),
        # )

        # print(f"subframe size {len(flatten_subframe)}")

        # for node in flatten_subframe:
        #     valid_constraint = carrier_world.universally_quantify(node, valid_constraint)

        # solver.add_assertion(valid_constraint)

        valuation_basis_size = 10 # count_modality(axiomatization)
        print(f"checking valuations with basis of size {valuation_basis_size}")

        carrier_world = complement_model.interpret_sort(sort_world)

        finite_worlds = tuple(smt.FreshSymbol(carrier_world.get_smt_sort()) for _ in range(valuation_basis_size))
        p_values = tuple(smt.FreshSymbol(smt.BOOL) for _ in range(valuation_basis_size))
        other_p_value = smt.FreshSymbol(smt.BOOL)

        # distinct_constraint = smt.And(
        #     smt.Not(smt.Equals(finite_worlds[i], finite_worlds[j]))
        #     for i in range(valuation_basis_size)
        #     for j in range(i)
        # )

        # neighborhood_constraint = smt.And(
        #     smt.Or(
        #         complement_model.interpret_relation(transition_symbol, finite_worlds[j], finite_worlds[i])
        #         for j in range(i)
        #     )
        #     for i in range(valuation_basis_size)
        # )

        p_relation = lambda world: smt.Or(
            smt.Or(
                smt.And(
                    smt.Equals(world, finite_worlds[i]),
                    p_values[i],
                )
                for i in range(valuation_basis_size)
            ),
            smt.Or(
                smt.And(
                    smt.And(
                        smt.Not(smt.Equals(world, finite_worlds[i]))
                        for i in range(valuation_basis_size)
                    ),
                    other_p_value,
                )
            ),
        )

        # need to quantify over all relations P
        constraint = smt.ForAll(p_values + (other_p_value,),
            axiomatization.interpret(
                modal.FOStructureFrame(complement_model, sort_world, transition_symbol),
                {
                    atom_p: p_relation,
                },
                finite_worlds[0],
            ),
        )

        for world_var in finite_worlds:
            constraint = carrier_world.universally_quantify(world_var, constraint)

        solver.add_assertion(constraint)

        print(f"is {axiomatization} complete", end="", flush=True)

        if solver.solve():
            print(" ... ✘")
        else:
            print(" ... ✓")
