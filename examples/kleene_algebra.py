from synthesis import * 
from synthesis.fol.cegis import CEGISynthesizer

theory_map = Parser.parse_theories(r"""
theory BOOLEAN-ALGEBRA
    sort Lattice

    function join: Lattice Lattice -> Lattice // \/
    function meet: Lattice Lattice -> Lattice // /\
    function comp: Lattice -> Lattice // negation
    constant top: Lattice
    constant bot: Lattice

    // commutativity
    axiom forall x: Lattice, y: Lattice. join(x, y) = join(y, x)
    axiom forall x: Lattice, y: Lattice. meet(x, y) = meet(y, x)

    // associativity
    axiom forall x: Lattice, y: Lattice, z: Lattice. join(x, join(y, z)) = join(join(x, y), z)
    axiom forall x: Lattice, y: Lattice, z: Lattice. meet(x, meet(y, z)) = meet(meet(x, y), z)

    // absorption
    axiom forall x: Lattice, y: Lattice. meet(x, join(x, y)) = x
    axiom forall x: Lattice, y: Lattice. join(x, meet(x, y)) = x

    // identity
    axiom forall x: Lattice. meet(x, bot()) = bot()
    axiom forall x: Lattice. join(x, top()) = top()

    // distributivity
    axiom forall x: Lattice, y: Lattice, z: Lattice. meet(x, join(y, z)) = join(meet(x, y), meet(x, z))
    axiom forall x: Lattice, y: Lattice, z: Lattice. join(x, meet(y, z)) = meet(join(x, y), join(x, z))

    // complements
    axiom forall x: Lattice. join(x, comp(x)) = top()
    axiom forall x: Lattice. meet(x, comp(x)) = bot()
end

theory KLEENE-ALGEBRA extending BOOLEAN-ALGEBRA
    function mul: Lattice Lattice -> Lattice
    function add: Lattice Lattice -> Lattice
    function star: Lattice -> Lattice
    relation eq: Lattice Lattice [smt("(= #1 #2)")]
    relation order: Lattice Lattice

    axiom forall x: Lattice, y: Lattice. mul(x,y) = meet(x,y)
    axiom forall x: Lattice, y: Lattice. add(x,y) = join(x,y)

    axiom forall x: Lattice. star(x) = top()
    axiom forall x: Lattice, y: Lattice. order(x,y) <-> add(x,y) = y
end
""")

# WTS: Boolean algebras are Kleene algebras with a*=1 for all a.

language = theory_map["KLEENE-ALGEBRA"].language.get_sublanguage(
    ("Lattice",),
    ("add", "mul", "bot", "top", "star"),
    ("eq","order"),
)

sort_lattice = language.get_sort("Lattice")

x = Variable("x", sort_lattice)
y = Variable("y", sort_lattice)
z = Variable("z", sort_lattice)

trivial_model = FiniteFOModelTemplate(Theory.empty_theory(language), size_bounds={ sort_lattice: 4 })
goal_model = FiniteFOModelTemplate(theory_map["KLEENE-ALGEBRA"], size_bounds={ sort_lattice: 4 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        # AtomicFormulaTemplate(language, (x,), 1),
        # AtomicFormulaTemplate(language, (x, y), 1),
        # AtomicFormulaTemplate(language, (x, y), 2),
        # AtomicFormulaTemplate(language, (x, y, z), 2),
        AtomicFormulaTemplate(language, (x, y, z), 3),
    ),
    trivial_model,
    goal_model,
): ...
