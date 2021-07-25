from typing import Any

from synthesis import smt
from synthesis.fol import *
from synthesis.synthesis import *
from synthesis.parser.parser import Parser


group_theory = Parser.parse_theory(r"""
theory GROUP
    sort Group

    constant id: Group
    function mul: Group Group -> Group
    function inv: Group -> Group

    relation eq: Group Group [smt("(= #1 #2)")]

    axiom forall x: Group. eq(mul(x, id()), x)
    axiom forall x: Group. eq(mul(id(), x), x)
    
    axiom forall x: Group, y: Group, z: Group. eq(mul(x, mul(y, z)), mul(mul(x, y), z))
    axiom forall x: Group. eq(mul(inv(x), x), id())
    axiom forall x: Group. eq(mul(x, inv(x)), id())
end
""")

ab_group_theory = Parser.parse_theory(r"""
theory ABELIAN_GROUP
    sort Group

    constant id: Group
    function mul: Group Group -> Group
    function inv: Group -> Group

    relation eq: Group Group [smt("(= #1 #2)")]

    axiom forall x: Group. eq(mul(x, id()), x)
    axiom forall x: Group. eq(mul(id(), x), x)
    
    axiom forall x: Group, y: Group. eq(mul(x, y), mul(y, x))
    
    axiom forall x: Group, y: Group, z: Group. eq(mul(x, mul(y, z)), mul(mul(x, y), z))
    axiom forall x: Group. eq(mul(inv(x), x), id())
    axiom forall x: Group. eq(mul(x, inv(x)), id())
end
""")

group_language = group_theory.language.get_sublanguage(
    ("Group",),
    ("id", "inv", "mul"),
    ("eq",),
)

sort_group = group_language.get_sort("Group")
assert sort_group is not None

x = Variable("x", sort_group)
y = Variable("y", sort_group)

# trivial_model = UninterpretedModelVariable(group_theory.language, smt.INT)
trivial_model = FiniteLFPModelVariable(group_theory, size_bounds={ sort_group: 8 })
# trivial_model = FOProvableModelVariable(group_theory, 0)
# goal_model = FOProvableModelVariable(theory, 0)
goal_model = FiniteLFPModelVariable(ab_group_theory, size_bounds={ sort_group: 8 })

for _ in CEIGSynthesizer().synthesize_for_model_classes(
    (
        AtomicFormulaVariable(group_language, (x, y), 1),
        AtomicFormulaVariable(group_language, (x, y), 2),
        # Implication(
        #     Conjunction(
        #         AtomicFormulaVariable(group_language, (x, y), 2),
        #         AtomicFormulaVariable(group_language, (x, y), 2),
        #     ),
        #     AtomicFormulaVariable(group_language, (x, y), 2),
        # ),
    ),
    trivial_model,
    goal_model,
): ...

