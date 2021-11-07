
from synthesis import * 
from synthesis.fol.cegis import CEGISynthesizer

theory_map = Parser.parse_theories(r"""
theory BTREE-ADT
    sort BTree
    constant leaf: BTree
    function node: BTree BTree -> BTree

    axiom forall t1: BTree, t2: BTree, t3: BTree, t4: BTree.
        node(t1, t2) = node(t3, t4) -> t1 = t3 /\ t2 = t4

    axiom forall t1: BTree, t2: BTree. leaf() != node(t1, t2)

    axiom forall t1: BTree, t2: BTree. t1 != node(t1, t2) /\ t2 != node(t1, t2)
end

theory BTREE-DESTRUCTOR extending BTREE-ADT
    relation isLeaf: BTree
    relation isNode: BTree

    function left: BTree -> BTree
    function right: BTree -> BTree

    axiom forall t: BTree. isLeaf(t) <-> t = leaf()
    axiom forall t: BTree. isNode(t) <-> exists t1: BTree, t2: BTree. t = node(t1, t2)

    axiom forall t1: BTree, t2: BTree. left(node(t1, t2)) = t1
    axiom forall t1: BTree, t2: BTree. right(node(t1, t2)) = t2
end
""")

theory = theory_map["BTREE-DESTRUCTOR"]

sort_btree = theory.language.get_sort("BTree")

language = theory.language.get_sublanguage(
    ("BTree",),
    (), # ("left", "right"),
    ("isLeaf",), # ("isLeaf", "isNode"),
)

x = Variable("x", sort_btree)
y = Variable("y", sort_btree)
z = Variable("z", sort_btree)

# trivial_model = FOProvableStructureTemplate(theory, unfold_depth=2)
# trivial_model = UninterpretedStructureTemplate(theory.language)
trivial_model = FiniteFOModelTemplate(Theory.empty_theory(language), size_bounds={ sort_btree: 5 })
goal_model = FiniteFOModelTemplate(theory, size_bounds={ sort_btree: 5 })

for _ in CEGISynthesizer().synthesize_for_model_classes(
    (
        AtomicFormulaTemplate(language, (x,), 0),
    ),
    trivial_model,
    goal_model,
): ...

