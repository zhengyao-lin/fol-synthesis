from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.prover import NaturalProof

from synthesis.fol.utils import FOLUtils

theory_map = Parser.parse_theories(r"""
theory BOOLEAN
    sort Boolean
    function join: Boolean Boolean -> Boolean // /\
    function meet: Boolean Boolean -> Boolean // \/
    function comp: Boolean -> Boolean // negation
    constant top: Boolean
    constant bot: Boolean

    relation eq: Boolean Boolean [smt("(= #1 #2)")]

    // commutativity
    axiom forall x: Boolean, y: Boolean. join(x, y) = join(y, x)
    axiom forall x: Boolean, y: Boolean. meet(x, y) = meet(y, x)

    // associativity
    axiom forall x: Boolean, y: Boolean, z: Boolean. join(x, join(y, z)) = join(join(x, y), z)
    axiom forall x: Boolean, y: Boolean, z: Boolean. meet(x, meet(y, z)) = meet(meet(x, y), z)

    // absorption
    axiom forall x: Boolean, y: Boolean. meet(x, join(x, y)) = x
    axiom forall x: Boolean, y: Boolean. join(x, meet(x, y)) = x

    // identity
    axiom forall x: Boolean. join(x, bot()) = bot()
    axiom forall x: Boolean. meet(x, top()) = top()

    // distributivity
    axiom forall x: Boolean, y: Boolean, z: Boolean. meet(x, join(y, z)) = join(meet(x, y), meet(x, z))
    axiom forall x: Boolean, y: Boolean, z: Boolean. join(x, meet(y, z)) = meet(join(x, y), join(x, z))

    // complements
    axiom forall x: Boolean. meet(x, comp(x)) = top()
    axiom forall x: Boolean. join(x, comp(x)) = bot()
end

theory UNINTERP
    sort Boolean
    function join: Boolean Boolean -> Boolean // /\
    function meet: Boolean Boolean -> Boolean // \/
    function comp: Boolean -> Boolean // negation
    constant top: Boolean
    constant bot: Boolean
end
""")

# want to find: axioms for the size-2 Boolean algebra
# which should give us all axioms for Boolean algebras

language = theory_map["BOOLEAN"].language.get_sublanguage(
    ("Boolean",),
    ("join", "meet", "comp", "top", "bot"),
    ("eq",),
)

language2 = theory_map["BOOLEAN"].language.get_sublanguage(
    ("Boolean",),
    ("join", "meet", "comp"),
    ("eq",),
)

sort_boolean = language.get_sort("Boolean")

x = Variable("x", sort_boolean)
y = Variable("y", sort_boolean)
z = Variable("z", sort_boolean)

trivial_model = FiniteFOModelTemplate(Theory.empty_theory(language), size_bounds={ sort_boolean: 4 }, exact_size=True)
goal_model = FiniteFOModelTemplate(theory_map["BOOLEAN"], size_bounds={ sort_boolean: 2 })

true_formulas = []

for formula, counterexample in CEGISynthesizer().synthesize_for_model_classes(
    (
        AtomicFormulaTemplate(language2, (x,), 1),
        AtomicFormulaTemplate(language, (x,), 1),
        AtomicFormulaTemplate(language2, (x, y), 1),
        AtomicFormulaTemplate(language, (x, y), 1),
        AtomicFormulaTemplate(language2, (x, y, z), 2),
        # AtomicFormulaTemplate(language, (x,), 1),
        # AtomicFormulaTemplate(language, (x, y), 1),
        # AtomicFormulaTemplate(language2, (x, y), 2),
        # AtomicFormulaTemplate(language, (x, y), 2),
        # AtomicFormulaTemplate(language, (x, y, z), 2),
    ),
    trivial_model,
    goal_model,
):
    if counterexample is None:
        true_formulas.append(Axiom(formula.quantify_all_free_variables()))

# except KeyboardInterrupt: pass
# except: pass

# # try to prove all boolean algebra axioms from the proposed theory
# proposed_theory = Theory(theory_map["BOOLEAN"].language, {}, tuple(true_formulas))

# print("\n\n################################################")

# for axiom in theory_map["BOOLEAN"].get_axioms():
#     extended_language, conjuncts = NaturalProof.encode_validity(proposed_theory, sort_boolean, axiom.formula, depth=1)
#     model = UninterpretedStructureTemplate(extended_language)

#     print(f"checking {axiom.formula} ...", end="", flush=True)

#     with smt.Solver("z3") as solver:
#         solver.add_assertion(model.get_constraint())

#         try:
#             for conjunct in conjuncts:
#                 free_vars = conjunct.get_free_variables()
#                 assignment = {
#                     var: model.interpret_sort(var.sort).get_fresh_constant(solver)
#                     for var in free_vars
#                 }

#                 solver.add_assertion(conjunct.interpret(model, assignment))
#                 if not solver.solve():
#                     print(" ✓")
#                     break
#             else:
#                 print(" ✘")
#         except KeyboardInterrupt: print("")
#         except: print("")
