from typing import Any

from synthesis import smt
from synthesis.fol import *
from synthesis.synthesis import *
from synthesis.parser.parser import Parser


theory = Parser.parse_theory(r"""
theory LIST
    sort Pointer

    constant nil: Pointer
    function n: Pointer -> Pointer

    relation list: Pointer
    relation lseg: Pointer Pointer
    relation in_lseg: Pointer Pointer Pointer

    relation eq: Pointer Pointer [smt("(= #1 #2)")]

    fixpoint in_lseg(x, y, z) = not eq(y, z) /\ (eq(x, y) \/ in_lseg(x, n(y), z))
    fixpoint list(x) = eq(x, nil()) \/ (list(n(x)) /\ not in_lseg(x, n(x), nil()))
    fixpoint lseg(x, y) = eq(x, y) \/ (lseg(n(x), y) /\ not in_lseg(x, n(x), y))
end
""")

language = theory.language.get_sublanguage(
    ("Pointer",),
    ("nil", "n"),
    ("list", "lseg"),
)

sort_pointer = language.get_sort("Pointer")
assert sort_pointer is not None

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

# free variables are universally quantified
template = Implication(
    Conjunction(
        AtomicFormulaVariable(language, (x, y, z), 0),
        AtomicFormulaVariable(language, (x, y, z), 0),
    ),
    AtomicFormulaVariable(language, (x, y, z), 0),
)

model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 4 })

for formula in CEIGSynthesizer(theory, template, model_var, 2).synthesize(): ...
    # print("### found", formula)
