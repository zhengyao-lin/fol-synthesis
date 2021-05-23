from z3 import *
from synthesis import *

env = Z3Environment(None)

ring_language = Language({ "add": 2, "0": 0, "1": 0 })

ring_z4 = Structure.from_finite_int(
    env,
    ring_language,
    { 0, 1, 2, 3 },
    {
        "add": lambda a, b: (a + b) % 4,
        # "mult": lambda a, b: (a * b) % 4,
        "1": 1,
        "0": 0,
    },
    {},
)

field_z3 = Structure.from_finite_int(
    env,
    ring_language,
    { 0, 1, 2 },
    {
        "add": lambda a, b: (a + b) % 3,
        # "mult": lambda a, b: (a * b) % 3,
        "1": 1,
        "0": 0,
    },
    {},
)

solver = Solver()

# find a term t with depth <= 3
# such that t = 1 in Z4 but t != 1 in Z3
solver.push()
term_var = TermVariable(env, ring_language, 4, 0)
solver.add(term_var.get_well_formedness_constraint())
solver.add(term_var.eval(ring_z4, ()) == ring_z4.eval_function("1", ()))
solver.add(term_var.eval(field_z3, ()) != field_z3.eval_function("1", ()))

if solver.check() == sat:
    print(term_var.unparse_z3_model(solver.model()))
else:
    print("unsat")
    
solver.pop()

# find an atomic formula phi with term depth <= 3
# such that phi is true in Z4 but not in Z3
solver.push()
atom_var = AtomicFormulaVariable(env, ring_language, 4, 0)
solver.add(atom_var.get_well_formedness_constraint())
solver.add(atom_var.eval(ring_z4, ()))
solver.add(Not(atom_var.eval(field_z3, ())))

if solver.check() == sat:
    print(atom_var.unparse_z3_model(solver.model()))
else:
    print("unsat")

solver.pop()
