from typing import Any

from synthesis import smt
from synthesis.fol.ast import *
from synthesis.synthesis import *
from synthesis.structure import *


sort_pointer = Sort("Pointer")
sort_int = Sort("Int", smt_hook=smt.INT)

nil_symbol = FunctionSymbol((), sort_pointer, "nil")
left_symbol = FunctionSymbol((sort_pointer,), sort_pointer, "left")
right_symbol = FunctionSymbol((sort_pointer,), sort_pointer, "right")
c_symbol = FunctionSymbol((), sort_int, "c")

key_symbol = FunctionSymbol((sort_pointer,), sort_int, "key")

btree_symbol = RelationSymbol((sort_pointer,), "btree")
bst_symbol = RelationSymbol((sort_pointer,), "bst")
leftmost_symbol = RelationSymbol((sort_pointer, sort_int), "leftmost")
in_bst_symbol = RelationSymbol((sort_pointer, sort_pointer), "in_bst")

le_int_symbol = RelationSymbol((sort_int, sort_int), "le_int", smt_hook=lambda x, y: smt.LE(x, y))
eq_int_symbol = RelationSymbol((sort_int, sort_int), "eq_int", smt_hook=lambda x, y: smt.Equals(x, y))

eq_pointer_symbol = RelationSymbol((sort_pointer, sort_pointer), "eq_pointer", smt_hook=lambda x, y: smt.Equals(x, y))
ne_pointer_symbol = RelationSymbol((sort_pointer, sort_pointer), "ne_pointer", smt_hook=lambda x, y: smt.Not(smt.Equals(x, y)))

synth_language = Language(
    (sort_pointer, sort_int),
    (nil_symbol, left_symbol, right_symbol, key_symbol, c_symbol),
    (btree_symbol, bst_symbol, leftmost_symbol, ne_pointer_symbol, le_int_symbol),
)

language = synth_language.expand(Language((), (), (in_bst_symbol, eq_int_symbol, eq_pointer_symbol)))

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)
v = Variable("v", sort_int)

nil = Application(nil_symbol, ())
left = lambda x: Application(left_symbol, (x,))
right = lambda x: Application(right_symbol, (x,))
key = lambda x: Application(key_symbol, (x,))
c = Application(c_symbol, ())

le_int = lambda x, y: RelationApplication(le_int_symbol, (x, y))
eq_int = lambda x, y: RelationApplication(eq_int_symbol, (x, y))

eq_pointer = lambda x, y: RelationApplication(eq_pointer_symbol, (x, y))
ne_pointer = lambda x, y: RelationApplication(ne_pointer_symbol, (x, y))

in_bst = lambda x, y: RelationApplication(in_bst_symbol, (x, y))
btree = lambda x: RelationApplication(btree_symbol, (x,))
bst = lambda x: RelationApplication(bst_symbol, (x,))
leftmost = lambda x, v: RelationApplication(leftmost_symbol, (x, v))

in_bst_defn = FixpointDefinition(
    in_bst_symbol,
    (x, y),
    Conjunction(
        ne_pointer(y, nil),
        Disjunction(
            eq_pointer(x, y),
            Disjunction(
                in_bst(x, left(y)),
                in_bst(x, right(y)),
            ),
        ),
    ),
)

btree_defn = FixpointDefinition(
    btree_symbol,
    (x,),
    Disjunction(
        eq_pointer(x, nil),
        Disjunction(
            Conjunction(
                eq_pointer(left(x), nil),
                eq_pointer(right(x), nil),
            ),
            Conjunction(
                Conjunction(
                    btree(left(x)),
                    btree(right(x)),
                ),
                Conjunction(
                    Negation(in_bst(x, left(x))),
                    Negation(in_bst(x, right(x))),
                ),
            )
        ),
    ),
)

bst_defn = FixpointDefinition(
    bst_symbol,
    (x,),
    Disjunction(
        eq_pointer(x, nil),
        Disjunction(
            Conjunction(
                eq_pointer(left(x), nil),
                eq_pointer(right(x), nil),
            ),
            Conjunction(
                Conjunction(
                    le_int(key(left(x)), key(x)),
                    le_int(key(x), key(right(x))),
                ),
                Conjunction(
                    Conjunction(
                        bst(left(x)),
                        bst(right(x)),
                    ),
                    Conjunction(
                        Negation(in_bst(x, left(x))),
                        Negation(in_bst(x, right(x))),
                    ),
                ),
            ),
        ),
    ),
)

leftmost_defn = FixpointDefinition(
    leftmost_symbol,
    (x, v),
    Disjunction(
        Conjunction(
            eq_pointer(left(x), nil),
            eq_int(key(x), v),
        ),
        Conjunction(
            ne_pointer(left(x), nil),
            leftmost(left(x), v),
        ),
    ),
)

theory = Theory(language, (in_bst_defn, btree_defn, bst_defn, leftmost_defn))

synt_var = ImplicationFormulaVariable(
    ConjunctionFormulaVariable((
        AtomicFormulaVariable(synth_language, (x,), 0),
        AtomicFormulaVariable(synth_language, (x,), 0),
        AtomicFormulaVariable(synth_language, (x,), 0),
    )),
    AtomicFormulaVariable(synth_language, (x,), 1),
)

model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 5 })

for formula in CEIGSynthesizer(theory, synt_var, model_var, 2).synthesize(): ...
    # print("### found", formula)
