# Discover FO properties on (R, <)
# which should give us the axioms for DLO w/o endpoints

# import sys
# sys.path.insert(0, "/home/rodlin/Desktop/illinois/research/learning-lfp/pysmt-fp")

from typing import Set

import itertools

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.prover import NaturalProof


float_theory = Parser.parse_theory(r"""
theory FLOAT
    sort Float [smt("(_ FloatingPoint 2 2)")]
    constant a: Float // for proving purposes

    relation eq: Float Float [smt("(= #1 #2)")]
    relation le: Float Float [smt("(fp.leq #1 #2)")]
    function add: Float Float -> Float [smt("(fp.add roundTowardZero #1 #2)")]
    relation isNormal: Float [smt("(fp.isNormal #1)")]
end
""")

uninterp_theory = Parser.parse_theory(r"""
theory UNINTERP
    sort Float
    constant a: Float
    relation eq: Float Float [smt("(= #1 #2)")]
    relation le: Float Float
    function add: Float Float -> Float
    relation isNormal: Float
end
""")

language = float_theory.language.get_sublanguage(
    ("Float",),
    ("add",),
    ("eq",),
)

language_le = float_theory.language.get_sublanguage(
    ("Float",),
    ("add",),
    ("eq", "le", "isNormal"),
)

sort_float32 = language.get_sort("Float")

x = Variable("x", sort_float32)
y = Variable("y", sort_float32)
z = Variable("z", sort_float32)
w = Variable("w", sort_float32)

templates = (
    # AtomicFormulaTemplate(language, (x, y), 0),
    # AtomicFormulaTemplate(language, (x, y), 1),
    # # AtomicFormulaTemplate(language, (x, y, z), 2),

    # Implication(
    #     AtomicFormulaTemplate(language_le, (x, y), 0),
    #     AtomicFormulaTemplate(language_le, (x, y, z), 1),
    # ),

    QuantifierFreeFormulaTemplate(language_le, (x, y, z), 0, 0),
    QuantifierFreeFormulaTemplate(language_le, (x, y, z), 0, 1),
    QuantifierFreeFormulaTemplate(language_le, (x, y, z), 1, 0),


    # Implication(
    #     Conjunction.from_conjuncts(
    #         RelationApplication(float_theory.language.get_relation_symbol("isNormal"), (x,)),
    #         RelationApplication(float_theory.language.get_relation_symbol("isNormal"), (y,)),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y), 0),
    # ),
    # Implication(
    #     Conjunction.from_conjuncts(
    #         RelationApplication(float_theory.language.get_relation_symbol("isNormal"), (x,)),
    #         RelationApplication(float_theory.language.get_relation_symbol("isNormal"), (y,)),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y), 1),
    # ),
    # Implication(
    #     Conjunction.from_conjuncts(
    #         RelationApplication(float_theory.language.get_relation_symbol("isNormal"), (x,)),
    #         RelationApplication(float_theory.language.get_relation_symbol("isNormal"), (y,)),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y), 2),
    # ),
    # Parser.parse_formula(language, "add(x:Float, y:Float) = add(y:Float, x:Float)"),
    # Implication(
    #     RelationApplication(
    #         language.get_relation_symbol("le"),
    #         (x, y),
    #     ),
    #     RelationApplication(
    #         language.get_relation_symbol("le"),
    #         (
    #             Application(language.get_function_symbol("roundTowardZero"), (x,)),
    #             Application(language.get_function_symbol("roundTowardZero"), (y,))
    #         ),
    #     )
    #     # AtomicFormulaTemplate(language, (x, y), 1),
    # ),
)

trivial_model = UninterpretedStructureTemplate(uninterp_theory.language)
std_model = FOModelTemplate(float_theory, {})

# for _ in CEGISynthesizer().synthesize_for_one_model(
#     templates,
#     trivial_model,
#     std_model,
#     np_indep_language=uninterp_theory.language,
#     np_indep_depth=2,
# ): ...

examples: Set[smt.SMTTerm] = set()

with smt.Solver(name="z3", logic="QF_UFFPA") as solver1, \
     smt.Solver(name="z3", logic="QF_UFFPA") as solver2, \
     smt.Solver(name="z3", logic="QF_UFFPA") as solver3:

    true_formulas: List[Formula] = []
    new_true_formulas: List[Formula] = []

    solver1.add_assertion(trivial_model.get_constraint())

    for template in templates:
        with smt.push_solver(solver1):
            print(f"### Template {template}")
            free_vars = tuple(template.get_free_variables())

            free_var_valuation1 = { var: trivial_model.interpret_sort(var.sort).get_fresh_constant(solver1) for var in free_vars }
            
            # re-add all true formulas
            new_true_formulas = true_formulas

            solver1.add_assertion(template.get_constraint())

            # non-trivial constraint
            solver1.add_assertion(smt.Not(template.interpret(trivial_model, free_var_valuation1)))

            while True:
                # print(examples)
                # the formula should hold on all examples
                for assignment in itertools.product(examples, repeat=len(free_vars)):
                    valuation = dict(zip(free_vars, assignment))
                    solver1.add_assertion(template.interpret(std_model, valuation))

                # avoid duplicate
                for true_formula in new_true_formulas:
                    formula_free_vars = tuple(true_formula.get_free_variables())

                    # term instantiation using free_var_valuation1
                    # TODO: this doesn't work right with pi-2 statements
                    for assignment in itertools.product(tuple(free_var_valuation1.values()), repeat=len(formula_free_vars)):
                        valuation = dict(zip(formula_free_vars, assignment))
                        solver1.add_assertion(true_formula.interpret(trivial_model, valuation))

                new_true_formulas = []

                # for assertion in solver1.assertions:
                #     assert smt.is_qfree(assertion)

                if not solver1.solve():
                    break

                candidate = template.get_from_smt_model(solver1.get_model())
                solver1.add_assertion(smt.Not(template.equals(candidate)))

                print(f"{candidate} ... ", end="", flush=True)

                # with smt.push_solver(solver3):
                #     # print("checking triviality")
                #     implication = Implication(
                #         Conjunction.from_conjuncts(*(
                #             true_formula.quantify_all_free_variables()
                #             for true_formula in true_formulas
                #         )),
                #         candidate.quantify_all_free_variables(),
                #     )

                #     extended_language, np_reducts = NaturalProof.encode_validity(
                #         uninterp_theory,
                #         uninterp_theory.language.get_sort("Float"),
                #         implication,
                #         2,
                #     )

                #     uninterp_model = UninterpretedStructureTemplate(extended_language, smt.INT)
                #     solver3.add_assertion(uninterp_model.get_constraint())

                #     for np_reduct in np_reducts:
                #         solver3.add_assertion(np_reduct.interpret(uninterp_model, {}))

                #     if not solver3.solve():
                #         # implication valid in FO, try next candidate
                #         print("d")
                #         solver1.add_assertion(smt.Not(template.equals(candidate)))
                #         continue
                #     print("nd, ", end="", flush=True)

                with smt.push_solver(solver2):
                    free_var_valuation2 = {
                        var: std_model.interpret_sort(var.sort).get_fresh_constant(solver2)
                        for var in candidate.get_free_variables()
                    }
                    # print(smt.Not(candidate.interpret(std_model, free_var_valuation2)).to_smtlib())
                    solver2.add_assertion(smt.Not(candidate.interpret(std_model, free_var_valuation2)))

                    # print(solver2.assertions)

                    if solver2.solve():
                        print("✘")
                        model = solver2.get_model()
                        for free_var in free_var_valuation2.values():
                            examples.add(model[free_var])
                    else:
                        print("✓")
                        true_formulas.append(candidate)
                        new_true_formulas.append(candidate)
