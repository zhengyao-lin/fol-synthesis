from z3 import *
from synthesis import *

env = Z3Environment(None)

# find a term that evaluates 0 in both monoids Z2 and Z3

monoid_language = Language({ "add": 2, "1": 0 })

term_var = TermVariable(env, monoid_language, 4, 0)

solver = Solver()
solver.add(term_var.get_well_formedness_constraint())

monoid_z2 = Structure.from_finite_int(
    env,
    monoid_language,
    { 0, 1 },
    {
        "add": {
            (0, 0): 0,
            (0, 1): 1,
            (1, 0): 1,
            (1, 1): 0,
        },
        "1": 1,
    },
    {}
)

monoid_z3 = Structure.from_finite_int(
    env,
    monoid_language,
    { 0, 1, 2 },
    {
        "add": lambda a, b: (a + b) % 3,
        "1": 1,
    },
    {}
)

solver.add(term_var.eval(monoid_z2, ()) == 0)
solver.add(term_var.eval(monoid_z3, ()) == 0)

print(solver.check())
print(term_var.unparse_z3_model(solver.model()))
