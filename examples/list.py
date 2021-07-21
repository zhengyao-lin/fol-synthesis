from typing import Any

from synthesis.smt import get_model, Solver, Not
from synthesis.fol.ast import *
from synthesis.synthesis import *
from synthesis.structure import *


sort_pointer = UninterpretedSort("Pointer")
sort_int = InterpretedSort("Int", "Int")

nil_symbol = FunctionSymbol((), sort_pointer, "nil")
next_symbol = FunctionSymbol((sort_pointer,), sort_pointer, "next")
list_symbol = RelationSymbol((sort_pointer,), "list")
lseg_symbol = RelationSymbol((sort_pointer, sort_pointer), "lseg")

language = Language(
    (sort_pointer,),
    (nil_symbol, next_symbol),
    (list_symbol, lseg_symbol),
)

finite_structure = SymbolicStructure(
    language,
    {
        sort_pointer: FiniteCarrierSet(smt.INT, (smt.Int(0), smt.Int(1), smt.Int(2), smt.Int(3), smt.Int(4))),
        sort_int: RefinementCarrierSet(smt.INT),
    },
    {
        nil_symbol: lambda: smt.Int(0),
        next_symbol: lambda p:
            smt.Ite(
                smt.Equals(p, smt.Int(0)),
                smt.Int(0),
            smt.Ite(
                smt.Equals(p, smt.Int(1)),
                smt.Int(0),
            smt.Ite(
                smt.Equals(p, smt.Int(2)),
                smt.Int(1),
            smt.Ite(
                smt.Equals(p, smt.Int(3)),
                smt.Int(3),
            smt.Ite(
                smt.Equals(p, smt.Int(4)),
                smt.Int(3),
                smt.Int(0),
            ))))),
    },
    {
        list_symbol: lambda p: smt.Or(
            smt.Equals(p, smt.Int(0)),
            smt.Equals(p, smt.Int(1)),
            smt.Equals(p, smt.Int(2)),
        ),
        lseg_symbol: lambda p1, p2: smt.Or(
            smt.And(smt.Equals(p1, smt.Int(0)), smt.Equals(p2, smt.Int(0))),
            smt.And(smt.Equals(p1, smt.Int(1)), smt.Equals(p2, smt.Int(0))),
            smt.And(smt.Equals(p1, smt.Int(2)), smt.Equals(p2, smt.Int(0))),
            smt.And(smt.Equals(p1, smt.Int(1)), smt.Equals(p2, smt.Int(1))),
            smt.And(smt.Equals(p1, smt.Int(2)), smt.Equals(p2, smt.Int(1))),
            smt.And(smt.Equals(p1, smt.Int(2)), smt.Equals(p2, smt.Int(2))),
            smt.And(smt.Equals(p1, smt.Int(3)), smt.Equals(p2, smt.Int(3))),
            smt.And(smt.Equals(p1, smt.Int(4)), smt.Equals(p2, smt.Int(3))),
            smt.And(smt.Equals(p1, smt.Int(4)), smt.Equals(p2, smt.Int(4))),
        ),
    },
)

x = Variable("x", sort_pointer)
y = Variable("y", sort_pointer)
z = Variable("z", sort_pointer)

free_vars = (x, y, z)

synt_var = ForAllBlockFormulaVariable(
    free_vars,
    ImplicationFormulaVariable(
        ConjunctionFormulaVariable((
            AtomicFormulaVariable(language, free_vars, 0),
            AtomicFormulaVariable(language, free_vars, 0),
        )),
        AtomicFormulaVariable(language, free_vars, 0),
    ),
)

with Solver(name="z3") as solver:
    synt_var.add_to_solver(solver)
    solver.add_assertion(synt_var.interpret_in_structure(finite_structure, {}))

    while solver.solve():
        model = solver.get_model()
        val = synt_var.get_from_model(model)
        print(val)
        solver.add_assertion(smt.Not(synt_var.equals(val)))
