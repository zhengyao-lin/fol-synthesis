import itertools

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.prover import NaturalProof


int_theory = Parser.parse_theory(r"""
theory INT
    sort Int [smt("Int")]
    function add: Int Int -> Int [smt("(+ #1 #2)")]
    relation le: Int Int [smt("(<= #1 #2)")]
    relation eq: Int Int [smt("(= #1 #2)")]
    constant zero: Int [smt("0")]
end
""")

uninterp_theory = Parser.parse_theory(r"""
theory UNINTERP
    sort Int
    function add: Int Int -> Int
    relation le: Int Int
    relation eq: Int Int [smt("(= #1 #2)")]
    constant zero: Int
end
""")

language = int_theory.language.get_sublanguage(
    ("Int",),
    ("add", "zero"),
    ("le",),
)

# le = lambda x, y: RelationApplication(int_theory.language.get_relation_symbol("le"), (x, y))
# upper = Application(int_theory.language.get_function_symbol("upper"), ())
# lower = Application(int_theory.language.get_function_symbol("lower"), ())

sort_int = language.get_sort("Int")

x = Variable("x", sort_int)
y = Variable("y", sort_int)
z = Variable("z", sort_int)

trivial_model = UninterpretedStructureTemplate(uninterp_theory.language, smt.INT)
std_model = FOModelTemplate(int_theory, {})

templates = (
    AtomicFormulaTemplate(language, (x, y), 0),
    AtomicFormulaTemplate(language, (x, y), 1),
    Implication(
        AtomicFormulaTemplate(language, (x, y), 0),
        AtomicFormulaTemplate(language, (x, y), 0),
    ),
    Implication(
        Conjunction(
            AtomicFormulaTemplate(language, (x, y, z), 0),
            AtomicFormulaTemplate(language, (x, y, z), 0),
        ),
        AtomicFormulaTemplate(language, (x, y, z), 0),
    ),

    # AtomicFormulaTemplate(language, (x, y, z), 2),
    # Implication(
    #     Conjunction.from_conjuncts(
    #         Conjunction(le(lower, x), le(x, upper)),
    #         Conjunction(le(lower, y), le(y, upper)),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y), 0),
    # ),
    # Implication(
    #     Conjunction.from_conjuncts(
    #         Conjunction(le(lower, x), le(x, upper)),
    #         Conjunction(le(lower, y), le(y, upper)),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y), 1),
    # ),
    # Implication(
    #     Conjunction.from_conjuncts(
    #         Conjunction(le(lower, x), le(x, upper)),
    #         Conjunction(le(lower, y), le(y, upper)),
    #         Conjunction(le(lower, z), le(z, upper)),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y, z), 1),
    # ),
)

examples = (smt.Int(0), smt.Int(1), smt.Int(2))

with smt.Solver(name="z3") as solver1, \
     smt.Solver(name="z3") as solver2, \
     smt.Solver(name="z3") as solver3:

    true_formulas: List[Formula] = []

    for template in templates:
        print(f"### Template {template}")
        free_vars = tuple(template.get_free_variables())

        free_var_valuation = { var: std_model.interpret_sort(var.sort).get_fresh_constant(solver2) for var in free_vars }

        with smt.push_solver(solver1):
            solver1.add_assertion(template.get_constraint())

            # the formula should hold on all examples
            for assignment in itertools.product(*((examples,) * len(free_vars))):
                valuation = dict(zip(free_vars, assignment))
                solver1.add_assertion(template.interpret(std_model, valuation))

            # solver1.push()

            while solver1.solve():
                candidate = template.get_from_smt_model(solver1.get_model())
                solver1.add_assertion(smt.Not(template.equals(candidate)))

                with smt.push_solver(solver3):
                    # print("checking triviality")
                    implication = Implication(
                        Conjunction.from_conjuncts(*(
                            true_formula.quantify_all_free_variables()
                            for true_formula in true_formulas
                        )),
                        candidate.quantify_all_free_variables(),
                    )

                    # print(implication)

                    extended_language, np_reducts = NaturalProof.encode_validity(
                        uninterp_theory,
                        uninterp_theory.language.get_sort("Int"),
                        implication,
                        2,
                    )

                    uninterp_model = UninterpretedStructureTemplate(extended_language, smt.INT)
                    solver3.add_assertion(uninterp_model.get_constraint())

                    for np_reduct in np_reducts:
                        solver3.add_assertion(np_reduct.interpret(uninterp_model, {}))

                    if not solver3.solve():
                        # implication valid in FO, try next candidate
                        continue

                # print(f"{candidate} ... ", end="", flush=True)
                # print(candidate)

                with smt.push_solver(solver2):
                    solver2.add_assertion(smt.Not(candidate.interpret(std_model, free_var_valuation)))

                    if not solver2.solve():
                        true_formulas.append(candidate)
                        print(candidate)

                    # if solver2.solve():
                    #     # print("✘")
                    #     # not valid
                    #     solver1.add_assertion(smt.Not(template.equals(candidate)))
                    # else:
                    #     # valid
                    #     # print("✓")

                    #     print(candidate)
                    #     true_formulas.append(candidate)
                    #     solver1.add_assertion(smt.Not(template.equals(candidate)))

                        # non-duplicate
                        # solver1.pop()
                        # solver1.push()

                        # extended, np_reducts = NaturalProof.encode_validity(
                        #     uninterp_theory,
                        #     sort_int,
                        #     Implication(
                        #         Conjunction.from_conjuncts(*(
                        #             true_formula.quantify_all_free_variables()
                        #             for true_formula in true_formulas
                        #         )),
                        #         template.quantify_all_free_variables(),
                        #     ),
                        #     2,
                        # )

                        # uninterp_model = UninterpretedStructureTemplate(extended, smt.INT)
                        
                        # for np_reduct in np_reducts:
                        #     print(np_reduct)
                        #     solver1.add_assertion(np_reduct.interpret(uninterp_model, free_var_valuation))

            # solver1.pop()


# for _ in CEGISynthesizer().synthesize_for_model_classes(
#     (
#         Implication(
#             Conjunction.from_conjuncts(
#                 Conjunction(le(lower, x), le(x, upper)),
#                 Conjunction(le(lower, y), le(y, upper)),
#             ),
#             AtomicFormulaTemplate(language, (x, y), 0),
#         ),
#         Implication(
#             Conjunction.from_conjuncts(
#                 Conjunction(le(lower, x), le(x, upper)),
#                 Conjunction(le(lower, y), le(y, upper)),
#             ),
#             AtomicFormulaTemplate(language, (x, y), 1),
#         ),
#         Implication(
#             Conjunction.from_conjuncts(
#                 Conjunction(le(lower, x), le(x, upper)),
#                 Conjunction(le(lower, y), le(y, upper)),
#                 Conjunction(le(lower, z), le(z, upper)),
#             ),
#             AtomicFormulaTemplate(language, (x, y, z), 1),
#         ),
#         # AtomicFormulaTemplate(language, (x, y), 2),
#         # Implication(
#         #     AtomicFormulaTemplate(language, (x, y), 0),
#         #     AtomicFormulaTemplate(language, (x, y), 1),
#         # ),
#         # Implication(
#         #     AtomicFormulaTemplate(language, (x, y), 1),
#         #     AtomicFormulaTemplate(language, (x, y), 1),
#         # ),
#     ),
#     trivial_model,
#     goal_model,
# ): ...

