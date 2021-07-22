from typing import Any

from synthesis import smt
from synthesis.fol.ast import *
from synthesis.synthesis import *
from synthesis.structure import *


sort_pointer = Sort("Pointer")

nil_symbol = FunctionSymbol((), sort_pointer, "nil")
next_symbol = FunctionSymbol((sort_pointer,), sort_pointer, "next")
list_symbol = RelationSymbol((sort_pointer,), "list")
lseg_symbol = RelationSymbol((sort_pointer, sort_pointer), "lseg")
in_lseg_symbol = RelationSymbol((sort_pointer, sort_pointer, sort_pointer), "in_lseg")
pointer_eq_symbol = RelationSymbol((sort_pointer, sort_pointer), "eq", smt_hook=lambda x, y: smt.Equals(x, y))

language = Language(
    (sort_pointer,),
    (nil_symbol, next_symbol),
    (list_symbol, lseg_symbol),
)

expanded_language = language.expand(Language((), (), (in_lseg_symbol, pointer_eq_symbol)))

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

# theory of list
in_lseg_defn = FixpointDefinition(
    in_lseg_symbol,
    (x, y, z),
    Conjunction(
        Negation(RelationApplication(pointer_eq_symbol, (y, z))), # y != z
        Disjunction(
            RelationApplication(pointer_eq_symbol, (x, y)), # x = y
            RelationApplication(in_lseg_symbol, (x, Application(next_symbol, (y,)), z)) # in_lseg(x, next(y), z)
        ),
    ),
)

list_defn = FixpointDefinition(
    list_symbol,
    (x,),
    Disjunction(
        RelationApplication(pointer_eq_symbol, (x, Application(nil_symbol, ()))), # x = nil
        Conjunction(
            RelationApplication(list_symbol, (Application(next_symbol, (x,)),)), # list(next(x))
            Negation(RelationApplication(in_lseg_symbol, (x, Application(next_symbol, (x,)), Application(nil_symbol, ())))) # not in_lseg(x, n(x), nil)
        ),
    ),
)

lseg_defn = FixpointDefinition(
    lseg_symbol,
    (x, y),
    Disjunction(
        RelationApplication(pointer_eq_symbol, (x, y)), # x = y
        Conjunction(
            RelationApplication(lseg_symbol, (Application(next_symbol, (x,)), y)), # lseg(next(x), y)
            Negation(RelationApplication(in_lseg_symbol, (x, Application(next_symbol, (x,)), y))), # not in_lseg(x, n(x), y)
        ),
    ),
)

theory = Theory(expanded_language, (in_lseg_defn, list_defn, lseg_defn))

# free variables are universally quantified
synt_var = ImplicationFormulaVariable(
    ConjunctionFormulaVariable((
        AtomicFormulaVariable(language, (x, y, z), 0),
        AtomicFormulaVariable(language, (x, y, z), 0),
    )),
    AtomicFormulaVariable(language, (x, y, z), 0),
)
model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 4 })

for formula in CEIGSynthesizer(theory, synt_var, model_var, 2).synthesize(): ...
    # print("### found", formula)
