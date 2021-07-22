from typing import Any

import itertools

from synthesis.smt import get_model, Solver, Not, Equals, BOOL, INT, FunctionType, FreshSymbol, Apply
from synthesis import smt
from synthesis.fol.ast import *
from synthesis.synthesis import *
from synthesis.structure import *


sort_pointer = Sort("Pointer")
sort_int = Sort("Int", INT)

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

def interpret_fixpoint_definition(definition: FixpointDefinition, structure: Structure) -> smt.SMTFunction:
    valuation = { var: smt.FreshSymbol(structure.interpret_sort(var.sort).get_smt_sort()) for var in definition.variables }
    smt_formula = structure.interpret_formula(definition.definition, valuation)

    def interp(*args: smt.SMTTerm) -> smt.SMTTerm:
        assert len(args) == len(definition.variables)
        substitution = { valuation[k]: v for k, v in zip(definition.variables, args) }
        return smt_formula.substitute(substitution) # substitution on the SMT formula

    return interp


nil_uninterp = smt.FreshFunction((), INT)
next_uninterp = smt.FreshFunction((INT,), INT)
list_uninterp = smt.FreshFunction((INT,), BOOL)
lseg_uninterp = smt.FreshFunction((INT, INT), BOOL)
in_lseg_uninterp = smt.FreshFunction((INT, INT, INT), BOOL)


fo_provable_counterexample_uninterp = SymbolicStructure(
    language,
    {
        sort_pointer: RefinementCarrierSet(INT),
    },
    {
        nil_symbol: nil_uninterp,
        next_symbol: next_uninterp,
    },
    {
        list_symbol: list_uninterp,
        lseg_symbol: lseg_uninterp,
        in_lseg_symbol: in_lseg_uninterp,
    },
)

fo_provable_counterexample = SymbolicStructure(
    language,
    {
        sort_pointer: RefinementCarrierSet(INT),
    },
    {
        nil_symbol: nil_uninterp,
        next_symbol: next_uninterp,
    },
    {
        list_symbol: interpret_fixpoint_definition(unfold_definition(list_defn, 2), fo_provable_counterexample_uninterp),
        lseg_symbol: interpret_fixpoint_definition(unfold_definition(lseg_defn, 2), fo_provable_counterexample_uninterp),
        in_lseg_symbol: interpret_fixpoint_definition(unfold_definition(in_lseg_defn, 2), fo_provable_counterexample_uninterp),
    },
)

theory = Theory(expanded_language, (in_lseg_defn, list_defn, lseg_defn))

model_var = FiniteLFPModelVariable(theory, size_bounds={ sort_pointer: 4 })

synthesized_formulas = []

with Solver(name="z3") as solver1, Solver(name="z3") as solver2, Solver(name="z3") as solver3:
    synt_var.add_to_solver(solver1)
    synt_var.add_to_solver(solver3)
    model_var.add_to_solver(solver2)

    solver1.add_assertion(Not(synt_var.interpret_in_structure(fo_provable_counterexample, {})))

    while solver1.solve():
        model1 = solver1.get_model()
        val = synt_var.get_from_model(model1)
        print(val, "... ", end="", flush=True)

        # try to find a finite counterexample
        solver2.add_assertion(smt.Not(model_var.interpret_formula(val)))
        if solver2.solve():
            model2 = solver2.get_model()
            counterexample = model_var.get_from_model(model2)
            
            # carrier = counterexample.carriers[sort_pointer]
            # print(carrier.domain)
            # print("nil", counterexample.interpret_function(nil_symbol))
            # print("next", tuple(counterexample.interpret_function(next_symbol, element) for element in carrier.domain))
            # print("list", tuple(element for element in carrier.domain if counterexample.interpret_relation(list_symbol, element).is_true()))
            # print("lseg", tuple((e1, e2) for e1 in carrier.domain for e2 in carrier.domain if counterexample.interpret_relation(lseg_symbol, e1, e2).is_true()))

            # add the new counterexample
            print("✘")
            solver1.add_assertion(synt_var.interpret_in_structure(counterexample, {}))
        else:
            # no counterexample found, maybe this is true
            print("✓")
            solver1.add_assertion(fo_provable_counterexample.interpret_formula(val))
