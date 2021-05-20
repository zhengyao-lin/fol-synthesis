from z3 import *
from synthesis import *

env = Z3Environment(None)

field_language = Language({ "add": 2, "mult": 2, "0": 0, "1": 0 })

solver = Solver()

field_z2 = Structure.from_finite_int(
    env,
    field_language,
    { 0, 1 },
    {
        "add": lambda a, b: (a + b) % 2,
        "mult": lambda a, b: (a * b) % 2,
        "1": 1,
        "0": 0,
    },
    {},
)

field_z3 = Structure.from_finite_int(
    env,
    field_language,
    { 0, 1, 2 },
    {
        "add": lambda a, b: (a + b) % 3,
        "mult": lambda a, b: (a * b) % 3,
        "1": 1,
        "0": 0,
    },
    {},
)

# find a term t with depth <= 3
# such that t = 1 in Z2 but t != 1 in Z3
term_var = TermVariable(env, field_language, 3, 0)
solver.add(term_var.get_well_formedness_constraint())
solver.add(term_var.eval(field_z2, ()) == field_z2.eval_function("1", ()))
solver.add(term_var.eval(field_z3, ()) != field_z3.eval_function("1", ()))

# find an atomic formula phi with term depth <= 3
# such that phi is true in Z2 but not in Z3
atom_var = AtomicFormulaVariable(env, field_language, 2, 0)
solver.add(atom_var.get_well_formedness_constraint())
solver.add(atom_var.eval(field_z2, ()))
solver.add(Not(atom_var.eval(field_z3, ())))

print(solver.check())
model = solver.model()

print(term_var.unparse_z3_model(model))
print(atom_var.unparse_z3_model(model))
