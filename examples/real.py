# Discover FO properties on (R, <)
# which should give us the axioms for DLO w/o endpoints

from typing import Set

import itertools

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.prover import NaturalProof


real_theory = Parser.parse_theory(r"""
theory REAL
    sort Real [smt("Real")]
    relation lt: Real Real [smt("(< #1 #2)")]
    relation eq: Real Real [smt("(= #1 #2)")]
end
""")

uninterp_theory = Parser.parse_theory(r"""
theory UNINTERP
    sort Real
    relation lt: Real Real
    relation eq: Real Real [smt("(= #1 #2)")]
end
""")

language = real_theory.language.get_sublanguage(
    ("Real",),
    (),
    ("lt", "eq"),
)

sort_real = language.get_sort("Real")

x = Variable("x", sort_real)
y = Variable("y", sort_real)
z = Variable("z", sort_real)
w = Variable("w", sort_real)

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

    # ExistentialQuantification(y, AtomicFormulaTemplate(language, (x, y), 0)),
    # ExistentialQuantification(y, Implication(
    #     AtomicFormulaTemplate(language, (x, y, z), 0),
    #     Conjunction(
    #         AtomicFormulaTemplate(language, (x, y, z), 0),
    #         AtomicFormulaTemplate(language, (x, y, z), 0),
    #     ),
    # )),
    # QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 2),

    QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 0),
    QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 1),
    QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 2),
    ExistentialQuantification(z, QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 0)),
    ExistentialQuantification(z, QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 1)),
    ExistentialQuantification(z, QuantifierFreeFormulaTemplate(language, (x, y, z), 0, 2)),
)

trivial_model = UninterpretedStructureTemplate(uninterp_theory.language)
std_model = FOModelTemplate(real_theory, {})

# for _ in CEGISynthesizer().synthesize_for_one_model(
#     templates,
#     trivial_model,
#     std_model,
#     np_indep_language=uninterp_theory.language,
#     np_indep_depth=2,
# ): ...

examples: Set[smt.SMTTerm] = set()

with smt.Solver(name="z3") as solver1, \
     smt.Solver(name="z3") as solver2:

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
