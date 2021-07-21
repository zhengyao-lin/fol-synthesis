from typing import Any

from synthesis.smt import get_model, Solver, Not, Equals, BOOL, INT, FunctionType, FreshSymbol, Apply
from synthesis import smt
from synthesis.fol.ast import *
from synthesis.synthesis import *
from synthesis.structure import *


sort_pointer = UninterpretedSort("Pointer")
sort_int = InterpretedSort("Int", INT)

nil_symbol = FunctionSymbol((), sort_pointer, "nil")
next_symbol = FunctionSymbol((sort_pointer,), sort_pointer, "next")
list_symbol = RelationSymbol((sort_pointer,), "list")
lseg_symbol = RelationSymbol((sort_pointer, sort_pointer), "lseg")
in_lseg_symbol = RelationSymbol((sort_pointer, sort_pointer, sort_pointer), "in_lseg")
pointer_eq_symbol = RelationSymbol((sort_pointer, sort_pointer), "eq", smt_hook=lambda x, y: Equals(x, y))

language = Language(
    (sort_pointer,),
    (nil_symbol, next_symbol),
    (list_symbol, lseg_symbol),
)

expanded_language = language.expand(Language((), (), (in_lseg_symbol, pointer_eq_symbol)))

finite_structure = SymbolicStructure(
    language,
    {
        sort_pointer: FiniteCarrierSet(smt.INT, (smt.Int(0), smt.Int(1), smt.Int(2), smt.Int(3), smt.Int(4))),
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

def unfold_definition(definition: FixpointDefinition, n: int) -> FixpointDefinition:
    formula = definition.definition

    for _ in range(n):
        formula = definition.unfold_in_formula(formula)

    return FixpointDefinition(
        definition.relation_symbol,
        definition.variables,
        formula,
    )

def interpret_fixpoint_definition(definition: FixpointDefinition, structure: Structure) -> Callable[..., smt.SMTTerm]:
    valuation = { var: smt.FreshSymbol(structure.interpret_sort(var.sort).get_smt_sort()) for var in definition.variables }
    smt_formula = structure.interpret_formula(definition.definition, valuation)

    def interp(*args: smt.SMTTerm) -> smt.SMTTerm:
        assert len(args) == len(definition.variables)
        substitution = { valuation[k]: v for k, v in zip(definition.variables, args) }
        return smt_formula.substitute(substitution) # substitution on the SMT formula

    return interp


nil_uninterp = FreshSymbol(FunctionType(INT, ()))
next_uninterp = FreshSymbol(FunctionType(INT, (INT,)))
list_uninterp = FreshSymbol(FunctionType(BOOL, (INT,)))
lseg_uninterp = FreshSymbol(FunctionType(BOOL, (INT, INT)))
in_lseg_uninterp = FreshSymbol(FunctionType(BOOL, (INT, INT, INT)))


counterexample_uninterp = SymbolicStructure(
    language,
    {
        sort_pointer: RefinementCarrierSet(INT),
    },
    {
        nil_symbol: lambda: nil_uninterp,
        next_symbol: lambda p: Apply(next_uninterp, (p,)),
    },
    {
        list_symbol: lambda p: Apply(list_uninterp, (p,)),
        lseg_symbol: lambda p1, p2: Apply(lseg_uninterp, (p1, p2)),
        in_lseg_symbol: lambda p1, p2, p3: Apply(in_lseg_uninterp, (p1, p2, p3)),
    },
)

counterexample = SymbolicStructure(
    language,
    {
        sort_pointer: RefinementCarrierSet(INT),
    },
    {
        nil_symbol: lambda: nil_uninterp,
        next_symbol: lambda p: Apply(next_uninterp, p),
    },
    {
        list_symbol: interpret_fixpoint_definition(unfold_definition(list_defn, 2), counterexample_uninterp),
        lseg_symbol: interpret_fixpoint_definition(unfold_definition(lseg_defn, 2), counterexample_uninterp),
        in_lseg_symbol: interpret_fixpoint_definition(unfold_definition(in_lseg_defn, 2), counterexample_uninterp),
    },
)

with Solver(name="z3") as solver:
    synt_var.add_to_solver(solver)
    solver.add_assertion(synt_var.interpret_in_structure(finite_structure, {}))
    solver.add_assertion(Not(synt_var.interpret_in_structure(counterexample, {})))

    while solver.solve():
        model = solver.get_model()
        val = synt_var.get_from_model(model)
        print(val)
        solver.add_assertion(smt.Not(synt_var.equals(val)))
        solver.add_assertion(counterexample.interpret_formula(val))
