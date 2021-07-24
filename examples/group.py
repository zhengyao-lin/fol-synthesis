from typing import Any

from synthesis import smt
from synthesis.fol import *
from synthesis.synthesis import *
from synthesis.parser.parser import Parser


theory = Parser.parse_theory(r"""
theory GROUP
    sort Group

    constant id: Group
    function mul: Group Group -> Group
    function inv: Group -> Group

    relation eq: Group Group [smt("(= #1 #2)")]

    axiom forall x: Group. eq(mul(x, id()), x)
    axiom forall x: Group. eq(mul(id(), x), x)
    
    // axiom forall x: Group, y: Group. eq(mul(x, y), mul(y, x))
    
    axiom forall x: Group, y: Group, z: Group. eq(mul(x, mul(y, z)), mul(mul(x, y), z))
    axiom forall x: Group. eq(mul(inv(x), x), id())
    axiom forall x: Group. eq(mul(x, inv(x)), id())
end
""")

language = theory.language.get_sublanguage(
    ("Group",),
    ("id", "inv"),
    ("eq",),
)

sort_group = language.get_sort("Group")
assert sort_group is not None

x = Variable("x", sort_group)

# free variables are universally quantified
# template = Implication(
#     AtomicFormulaVariable(language, (x,), 1),
#     AtomicFormulaVariable(language, (x,), 2),
# )

template = AtomicFormulaVariable(language, (x,), 2)

model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_group: 10 })

for formula in CEIGSynthesizer(theory, template, model_var, 0).synthesize(include_fo_provable=True, remove_fo_duplicate=True): ...
    # print("### found", formula)

