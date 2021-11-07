from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


theory = Parser.parse_theory(r"""
theory NAT
    sort Nat

    constant undefined: Nat

    constant Z: Nat
    function S: Nat -> Nat

    relation boundary: Nat
    relation wellformed: Nat
    relation eq: Nat Nat [smt("(= #1 #2)")]

    axiom forall x: Nat, y: Nat. not boundary(x) /\ not boundary(y) /\ S(x) = S(y) -> x = y
    axiom forall x: Nat. x != undefined() -> S(x) != x

    axiom not boundary(undefined())

    axiom forall x: Nat. boundary(x) -> S(x) = undefined()
    axiom Z() != undefined()
    axiom S(undefined()) = undefined()

    fixpoint wellformed(x) = x = Z() \/ exists y: Nat. wellformed(y) /\ x = S(y)
    axiom forall x: Nat. wellformed(x)

    // functions
    relation add: Nat Nat Nat
    fixpoint add(x, y, z) =
        ((x = undefined() \/ y = undefined()) /\ z = undefined()) \/
        (y = Z() /\ z = x) \/
        (exists w1: Nat, w2: Nat. y != undefined() /\ y = S(w1) /\ add(x, w1, w2) /\ z = S(w2))

    // relation mul: Nat Nat Nat
    // fixpoint mul(x, y, z) =
    //     ((x = undefined() \/ y = undefined()) /\ z = undefined()) \/
    //     (x != undefined() /\ y = Z() /\ z = Z()) \/
    //     (x != undefined() /\ y = S(Z()) /\ z = x) \/
    //     (exists w1: Nat, w2: Nat. y != undefined() /\ y = S(S(w1)) /\ mul(x, S(w1), w2) /\ add(x, w2, z))

    axiom S(S(S(S(Z())))) != undefined()
end
""")

sort_nat = theory.language.get_sort("Nat")

boundary = lambda x: RelationApplication(theory.language.get_relation_symbol("boundary"), (x,))

language = theory.language.get_sublanguage(
    ("Nat",),
    (),
    ("add",),
)

x = Variable("x", sort_nat)
y = Variable("y", sort_nat)
z = Variable("z", sort_nat)

# trivial_model = FOProvableStructureTemplate(theory, unfold_depth=2)
# trivial_model = UninterpretedStructureTemplate(theory.language)
trivial_model = FiniteFOModelTemplate(Theory.empty_theory(theory.language), size_bounds={ sort_nat: 5 })
goal_model = FiniteLFPModelTemplate(theory, size_bounds={ sort_nat: 5 })

# with smt.Solver(name="z3") as solver:
#     solver.add_assertion(goal_model.get_constraint())

#     solver.solve()
#     model = goal_model.get_from_smt_model(solver.get_model())

#     print(model)

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        AtomicFormulaTemplate(language, (x,), 0),
        # Implication(
        #     AtomicFormulaTemplate(language, (x, y, z), 0),
        #     AtomicFormulaTemplate(language, (x, y, z), 0),
        # ),
        # Implication(
        #     Conjunction(
        #         AtomicFormulaTemplate(language, (x, y, z), 0),
        #         AtomicFormulaTemplate(language, (x, y, z), 0),
        #     ),
        #     AtomicFormulaTemplate(language, (x, y, z), 0),
        # ),
        # Implication(
        #     RelationApplication(language.get_relation_symbol("add"), (x, y, z)),
        #     RelationApplication(language.get_relation_symbol("add"), (y, x, z)),
        # ),
        # Implication(
        #     RelationApplication(theory.language.get_relation_symbol("mul"), (x, y, z)),
        #     RelationApplication(theory.language.get_relation_symbol("mul"), (y, x, z)),
        # ),
    ),
    trivial_model,
    goal_model,
): ...
