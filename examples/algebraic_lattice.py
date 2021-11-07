from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


# Lattice as an algebraic structure
theory_map = Parser.parse_theories(r"""
theory LATTICE-LANGUAGE
    sort Lattice

    function join: Lattice Lattice -> Lattice
    function meet: Lattice Lattice -> Lattice

    relation le_join: Lattice Lattice
    relation le_meet: Lattice Lattice
    relation eq: Lattice Lattice [smt("(= #1 #2)")]

    axiom forall x: Lattice, y: Lattice. le_join(x, y) <-> x = join(x, y)
    axiom forall x: Lattice, y: Lattice. le_meet(x, y) <-> y = meet(x, y)
end

theory JOIN-SEMILATTICE extending LATTICE-LANGUAGE
    axiom forall x: Lattice, y: Lattice. join(x, y) = join(y, x)
    axiom forall x: Lattice, y: Lattice, z: Lattice. join(x, join(y, z)) = join(join(x, y), z)
    axiom forall x: Lattice. join(x, x) = x
end

theory MEET-SEMILATTICE extending LATTICE-LANGUAGE
    axiom forall x: Lattice, y: Lattice. meet(x, y) = meet(y, x)
    axiom forall x: Lattice, y: Lattice, z: Lattice. meet(x, meet(y, z)) = meet(meet(x, y), z)
    axiom forall x: Lattice. meet(x, x) = x
end

theory LATTICE extending JOIN-SEMILATTICE MEET-SEMILATTICE
end
""")

# WTS:
# 1. a lattice is a partial order
# 2. any two element has a least upper bound
# 3. any two element has a greatest lower bound

lattice_language = theory_map["LATTICE-LANGUAGE"].language

join_semilattice = theory_map["JOIN-SEMILATTICE"]
lattice = theory_map["LATTICE"]

order_language = lattice_language.get_sublanguage(
    ("Lattice",),
    (),
    ("le_join", "eq"),
)

sort_lattice = order_language.get_sort("Lattice")

x = Variable("x", sort_lattice)
y = Variable("y", sort_lattice)
z = Variable("z", sort_lattice)

trivial_model = FiniteFOModelTemplate(Theory.empty_theory(order_language), size_bounds={ sort_lattice: 4 })
goal_model = FiniteFOModelTemplate(lattice, size_bounds={ sort_lattice: 4 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        QuantifierFreeFormulaTemplate(order_language, (x, y), 0, 0),
        QuantifierFreeFormulaTemplate(order_language, (x, y), 0, 1),
        QuantifierFreeFormulaTemplate(order_language, (x, y, z), 0, 2),
        ExistentialQuantification(z, QuantifierFreeFormulaTemplate(order_language, (x, y, z), 0, 2)),

        # AtomicFormulaTemplate(order_language, (x, y), 1),
        # Implication(
        #     Conjunction(
        #         AtomicFormulaTemplate(order_language, (x, y, z), 1),
        #         AtomicFormulaTemplate(order_language, (x, y, z), 1),
        #     ),
        #     AtomicFormulaTemplate(order_language, (x, y, z), 1),
        # ),
        # ExistentialQuantification(
        #     z,
        #     Conjunction(
        #         AtomicFormulaTemplate(order_language, (x, y, z), 1),
        #         AtomicFormulaTemplate(order_language, (x, y, z), 1),
        #     ),
        # ),
    ),
    trivial_model,
    goal_model,
): ...

