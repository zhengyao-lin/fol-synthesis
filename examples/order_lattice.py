from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer


# Lattice as an order
theory_map = Parser.parse_theories(r"""
theory LATTICE-LANGUAGE
    sort Lattice

    relation le: Lattice Lattice

    function join: Lattice Lattice -> Lattice
    function meet: Lattice Lattice -> Lattice

    relation eq: Lattice Lattice [smt("(= #1 #2)")]
end

theory PARTIAL-ORDER extending LATTICE-LANGUAGE
    axiom forall x: Lattice. le(x, x)
    axiom forall x: Lattice, y: Lattice. le(x, y) /\ le(y, x) -> x = y
    axiom forall x: Lattice, y: Lattice, z: Lattice. le(x, y) /\ le(y, z) -> le(x, z)
end

theory JOIN-SEMILATTICE extending PARTIAL-ORDER
    axiom forall x: Lattice, y: Lattice, z: Lattice. le(join(x, y), x) /\ le(join(x, y), y) /\ (le(z, x) /\ le(z, y) -> le(z, join(x, y)))
end

theory MEET-SEMILATTICE extending PARTIAL-ORDER
    axiom forall x: Lattice, y: Lattice, z: Lattice. le(x, meet(x, y)) /\ le(y, meet(x, y)) /\ (le(x, z) /\ le(y, z) -> le(meet(x, y), z))
end

theory LATTICE extending JOIN-SEMILATTICE MEET-SEMILATTICE
end
""")

# WTS: a lattice has an algebraic structure

lattice_language = theory_map["LATTICE-LANGUAGE"].language

join_semilattice = theory_map["JOIN-SEMILATTICE"]
lattice = theory_map["LATTICE"]

order_language = lattice_language.get_sublanguage(
    ("Lattice",),
    ("join", "meet"),
    ("eq",),
)

sort_lattice = order_language.get_sort("Lattice")

x = Variable("x", sort_lattice)
y = Variable("y", sort_lattice)
z = Variable("z", sort_lattice)

trivial_model = FiniteFOModelTemplate(Theory.empty_theory(order_language), size_bounds={ sort_lattice: 4 })
goal_model = FiniteFOModelTemplate(lattice, size_bounds={ sort_lattice: 4 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        AtomicFormulaTemplate(order_language, (x,), 1),
        AtomicFormulaTemplate(order_language, (x, y), 1),
        AtomicFormulaTemplate(order_language, (x, y), 2),
        AtomicFormulaTemplate(order_language, (x, y, z), 2),
    ),
    trivial_model,
    goal_model,
): ...

