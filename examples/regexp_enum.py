import time
import subprocess

from .regexp import ka_sort, check_regex_equivalence
from synthesis import *
from synthesis.fol.utils import FOLUtils

vampire_binary = "/home/rodlin/Desktop/illinois/research/learning-lfp/vampire/vampire_z3_Release_static_master_4764"

ka_theory = Parser.parse_theory(r"""
theory KLEENE-ALGEBRA
    sort KA
    relation eq: KA KA [smt("(= #1 #2)")]

    constant zero: KA [smt("zero")] // empty language
    constant one: KA [smt("one")] // language with an empty word
    function union: KA KA -> KA [smt("(union #1 #2)")]
    function concat: KA KA -> KA [smt("(concat #1 #2)")]
    function closure: KA -> KA [smt("(closure #1)")]
end
""")

def print_equation_in_tptp(equation: Formula):
    """
    Print an equation in TPTP format
    """
    free_vars = list(equation.get_free_variables())
    free_vars_names_upper = [ var.name.upper() for var in free_vars ]
    free_vars_replacement = { var: Variable(var.name.upper(), var.sort) for var in free_vars }
    
    body = str(equation.substitute(free_vars_replacement)).replace(":KA", "").replace("()", "")

    if len(free_vars) != 0:
        return f"! [{', '.join(free_vars_names_upper)}] : {body}"

    return body

def check_equation_implication(equational_theory: Tuple[Equality, ...], equation: Equality) -> bool:
    """
    Return True if the implication is valid, otherwise return False (or if the result is unknown/timeout)
    """

#     prelude = b"""
# (declare-sort KA 0)

# (declare-fun union (KA KA) KA)
# (declare-fun concat (KA KA) KA)
# (declare-fun closure (KA) KA)
# (declare-const one KA)
# (declare-const zero KA)
# """

    # trivial_model = UninterpretedStructureTemplate(language, default_sort=smt.Type("KA"))

    # fof(kozen_3, axiom, ! [A, B, C] : plus(A, plus(B, C)) = plus(plus(A, B), C)).

    proc = subprocess.Popen(
        [ vampire_binary, "--mode", "casc", "-t", "5s" ],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    # proc.stdin.write(prelude)
    for i, axiom in enumerate(equational_theory):
        # print(print_equation_in_tptp(axiom))
        proc.stdin.write(f"fof(axiom_{i}, axiom, {print_equation_in_tptp(axiom)}).".encode())

    proc.stdin.write(f"fof(conjecture, conjecture, {print_equation_in_tptp(equation)}).".encode())

    proc.stdin.close()
    stdout = proc.stdout.read()

    exit_code = proc.wait()
    if exit_code != 0:
        raise Exception(f"vampire failed with {exit_code}")

    # print(stdout.decode())

    return b"Termination reason: Refutation\n" in stdout


def remove_dependent_axioms(axioms: Iterable[Formula]) -> Tuple[Formula, ...]:
    independent_axioms = []
    unknown = list(axioms)

    while len(unknown) != 0:
        axiom = unknown.pop()

        if not check_equation_implication(tuple(unknown + independent_axioms), axiom):
            print("independent", axiom)
            independent_axioms.append(axiom)
        else:
            print("dependent", axiom)

    return tuple(independent_axioms)


def find_axioms(language: Language, lhs_depth: int, rhs_depth: int, free_vars: Tuple[Variable, ...], initial_axioms: Tuple[Formula, ...]) -> Tuple[Formula, ...]:
    lhs_set = list(FOLUtils.get_ground_terms_in_language(language, lhs_depth, free_vars)[ka_sort])
    rhs_set = list(FOLUtils.get_ground_terms_in_language(language, rhs_depth, free_vars)[ka_sort])

    total_num_equalities = len(lhs_set) * len(rhs_set)
    print(f"enumerating {len(lhs_set)} x {len(rhs_set)} = {total_num_equalities} equations")

    num_tried = 0
    found_axioms = list(initial_axioms)

    start = time.time()

    for lhs in lhs_set:
        for rhs in rhs_set:
            equality = Equality(lhs, rhs)

            num_tried += 1

            if num_tried % 10 == 0:
                time_elapsed = time.time() - start
                print(f"\33[2K\r[{num_tried} / {total_num_equalities}], {round(time_elapsed, 2)}s spent, total est {round(total_num_equalities / (num_tried / time_elapsed), 2)}s", end="", flush=True)

            if check_regex_equivalence(lhs, rhs):
                dependent = check_equation_implication(found_axioms, equality)

                if not dependent:
                    print(f"\33[2K\r{equality}")
                    found_axioms.append(equality)

    print("\33[2K\r", end="")

    print(f"enumeration took {time.time() - start}s")
    print()
    start = time.time()

    # prune dependent axioms
    final_axioms = remove_dependent_axioms(found_axioms)

    print(f"dependence check took {time.time() - start}s")
    print()

    return final_axioms



# print(check_equation_implication(
#     (Parser.parse_formula(language, "union(a:KA, b:KA) = union(b:KA, a:KA)"),),
#     Parser.parse_formula(language, "union(a:KA, zero()) = union(one(), a:KA)"),
# ))
# exit()

c2_d2_equalities = find_axioms(ka_theory.language.get_sublanguage(
    ("KA",),
    ("union", "concat", "closure", "one", "zero"),
    (),
), 2, 2, (Variable("a", ka_sort), Variable("b", ka_sort)), ())

final_axioms = find_axioms(ka_theory.language.get_sublanguage(
    ("KA",),
    ("union", "concat", "closure"),
    (),
), 3, 3, (Variable("a", ka_sort), Variable("b", ka_sort), Variable("c", ka_sort)), c2_d2_equalities)

print("final axioms:")
for axiom in final_axioms:
    print(axiom)
