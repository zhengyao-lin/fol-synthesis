from typing import Set

import itertools

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.prover import NaturalProof


nat_theory = Parser.parse_theory(r"""
theory NAT
    sort Nat [smt("Int", "(>= #1 0)")]
    function add: Nat Nat -> Nat [smt("(+ #1 #2)")]
    function mul: Nat Nat -> Nat [smt("(* #1 #2)")]
    relation le: Nat Nat [smt("(<= #1 #2)")]
    relation eq: Nat Nat [smt("(= #1 #2)")]
    constant zero: Nat [smt("0")]
    constant one: Nat [smt("1")]
end
""")

uninterp_theory = Parser.parse_theory(r"""
theory UNINTERP
    sort Nat
    function add: Nat Nat -> Nat
    function mul: Nat Nat -> Nat
    relation le: Nat Nat
    relation eq: Nat Nat [smt("(= #1 #2)")]
    constant zero: Nat
    constant one: Nat
end
""")

language = nat_theory.language.get_sublanguage(
    ("Nat",),
    ("add", "zero", "one"),
    ("eq", "le"),
)

# language_zero = nat_theory.language.get_sublanguage(
#     ("Nat",),
#     ("add", "mul", "zero"),
#     ("eq",),
# )

# language_one = nat_theory.language.get_sublanguage(
#     ("Nat",),
#     ("add", "mul", "one"),
#     ("eq",),
# )

# language_one_zero = nat_theory.language.get_sublanguage(
#     ("Nat",),
#     ("add", "mul", "zero", "one"),
#     ("eq",),
# )

sort_nat = language.get_sort("Nat")

x = Variable("x", sort_nat)
y = Variable("y", sort_nat)
z = Variable("z", sort_nat)

templates = (
    # AtomicFormulaTemplate(language, (x, y), 0),
    # AtomicFormulaTemplate(language, (x, y), 1),
    # Implication(
    #     AtomicFormulaTemplate(language, (x, y), 0),
    #     AtomicFormulaTemplate(language, (x, y), 0),
    # ),
    # Implication(
    #     Conjunction(
    #         AtomicFormulaTemplate(language, (x, y, z), 0),
    #         AtomicFormulaTemplate(language, (x, y, z), 0),
    #     ),
    #     AtomicFormulaTemplate(language, (x, y, z), 0),
    # ),
    # AtomicFormulaTemplate(language, (), 0),
    # AtomicFormulaTemplate(language, (), 1),
    # AtomicFormulaTemplate(language, (), 2),
    QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 0),
    QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 1),
    QuantifierFreeFormulaTemplate(language, (x, y, z), 1, 0),
    QuantifierFreeFormulaTemplate(language, (x, y, z), 1, 1),
    # ExistentialQuantification(z, QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 0)),
    # ExistentialQuantification(z, QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 1)),
    # ExistentialQuantification(z, QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 2)),
)

trivial_model = UninterpretedStructureTemplate(uninterp_theory.language)
std_model = FOModelTemplate(nat_theory, {})

# for _ in CEGISynthesizer(check_no_quantifiers=True).synthesize_for_one_model(
#     templates,
#     trivial_model,
#     std_model,
#     np_indep_language=uninterp_theory.language,
#     np_indep_depth=2,
# ): ...

examples: Set[smt.SMTTerm] = set()

with smt.Solver(name="z3") as solver1, \
     smt.Solver(name="z3") as solver2, \
     smt.Solver(name="z3") as solver3:

    true_formulas: List[Formula] = []
    new_true_formulas: List[Formula] = []

    solver1.add_assertion(trivial_model.get_constraint())

    # find all constant interpretations in the trivial model
    constants = []
    for function_symbol in uninterp_theory.language.function_symbols:
        if len(function_symbol.input_sorts) == 0:
            constants.append(Application(function_symbol, ()).interpret(trivial_model, {}))

    for template in templates:
        with smt.push_solver(solver1):
            print(f"### Template {template}")
            free_vars = tuple(template.get_free_variables())

            free_var_valuation1 = { var: trivial_model.interpret_sort(var.sort).get_fresh_constant(solver1) for var in free_vars }
            free_var_valuation2 = { var: std_model.interpret_sort(var.sort).get_fresh_constant(solver2) for var in free_vars }
            
            # re-add all true formulas
            new_true_formulas = true_formulas

            solver1.add_assertion(template.get_constraint())

            # non-trivial constraint
            solver1.add_assertion(smt.Not(template.interpret(trivial_model, free_var_valuation1)))

            while True:
                # the formula should hold on all examples
                for assignment in itertools.product(examples, repeat=len(free_vars)):
                    valuation = dict(zip(free_vars, assignment))
                    solver1.add_assertion(template.interpret(std_model, valuation))

                # avoid duplicate
                for true_formula in new_true_formulas:
                    formula_free_vars = tuple(true_formula.get_free_variables())

                    # term instantiation using free_var_valuation1
                    ground_terms = tuple(free_var_valuation1.values()) + tuple(constants)

                    for assignment in itertools.product(ground_terms, repeat=len(formula_free_vars)):
                        valuation = dict(zip(formula_free_vars, assignment))
                        solver1.add_assertion(true_formula.interpret(trivial_model, valuation))

                new_true_formulas = []

                # for assertion in solver1.assertions:
                #     assert smt.is_qfree(assertion)

                if not solver1.solve():
                    break

                candidate = template.get_from_smt_model(solver1.get_model())

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
                #         uninterp_theory.language.get_sort("Nat"),
                #         implication,
                #         2,
                #     )

                #     uninterp_model = UninterpretedStructureTemplate(extended_language, smt.INT)
                #     solver3.add_assertion(uninterp_model.get_constraint())

                #     for np_reduct in np_reducts:
                #         solver3.add_assertion(np_reduct.interpret(uninterp_model, {}))

                #     if not solver3.solve():
                #         # implication valid in FO, try next candidate
                #         print("duplicate")
                #         solver1.add_assertion(smt.Not(template.equals(candidate)))
                #         continue

                with smt.push_solver(solver2):
                    solver2.add_assertion(smt.Not(candidate.interpret(std_model, free_var_valuation2)))

                    if not solver2.solve():
                        print("✓")
                        true_formulas.append(candidate)
                        new_true_formulas.append(candidate)
                    else:
                        print("✘")
                        model = solver2.get_model()

                        for free_var in free_var_valuation2.values():
                            examples.add(model[free_var])
