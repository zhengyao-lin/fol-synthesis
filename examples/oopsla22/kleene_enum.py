import time
import argparse
import subprocess

from synthesis import *


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


def check_equation_implication(
    equational_theory: Tuple[Equality, ...],
    equation: Equality,
    vampire_binary: str = "vampire",
) -> bool:
    """
    Return True if the implication is valid, otherwise return False (or if the result is unknown/timeout)
    """

    proc = subprocess.Popen(
        [ vampire_binary, "--mode", "casc_sat", "-t", "5s" ],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    # proc.stdin.write(prelude)
    for i, axiom in enumerate(equational_theory):
        # print(print_equation_in_tptp(axiom))
        proc.stdin.write(f"fof(axiom_{i}, axiom, {print_equation_in_tptp(axiom)}).".encode())

    proc.stdin.write(f"fof(conjecture, conjecture, {print_equation_in_tptp(equation)}).".encode())
    proc.stdin.close()

    try:
        proc.wait(timeout=5)

    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()

    # if exit_code != 0:
    #     raise Exception(f"vampire failed with {exit_code}")

    # print(stdout.decode())

    return b"Termination reason: Refutation\n" in proc.stdout.read()


def remove_dependent_axioms(
    axioms: Iterable[Formula],
    **vampire_args,
) -> Tuple[Formula, ...]:
    independent_axioms = []
    unknown = list(axioms)

    while len(unknown) != 0:
        axiom = unknown.pop()

        if not check_equation_implication(tuple(unknown + independent_axioms), axiom, **vampire_args):
            print("independent", axiom)
            independent_axioms.append(axiom)
        else:
            print("dependent", axiom)

    return tuple(independent_axioms)


def find_axioms(
    language: Language,
    primary_sort: Sort,
    canonical_structure: Structure,
    lhs_depth: int,
    rhs_depth: int,
    free_vars: Tuple[Variable, ...],
    free_var_constants: Tuple[FunctionSymbol, ...], # constant symbols corresponding to the free vars
    initial_axioms: Tuple[Formula, ...],
    **vampire_args,
) -> Tuple[Formula, ...]:
    lhs_set = [ term for _, term in TermTemplate(language, free_vars, lhs_depth, primary_sort).enumerate() ]
    rhs_set = [ term for _, term in TermTemplate(language, free_vars, rhs_depth, primary_sort).enumerate() ]

    total_num_equalities = len(lhs_set) * len(rhs_set)
    print(f"enumerating {len(lhs_set)} x {len(rhs_set)} = {total_num_equalities} equations")

    num_tried = 0
    found_axioms = list(initial_axioms)

    start = time.time()

    with smt.Solver(name="z3") as solver:
        # interpreting the constants in the canonical structures
        free_var_constant_interps = tuple(
            Application(constant, ()).interpret(canonical_structure, {})
            for constant in free_var_constants
        )

        free_var_map_to_constants = dict(zip(free_vars, free_var_constant_interps))

        for lhs in lhs_set:
            for rhs in rhs_set:
                equality = Equality(lhs, rhs)

                num_tried += 1

                if num_tried % 10 == 0:
                    time_elapsed = time.time() - start
                    print(f"\33[2K\r[{num_tried} / {total_num_equalities}], {round(time_elapsed, 2)}s spent, total est {round(total_num_equalities / (num_tried / time_elapsed), 2)}s", end="", flush=True)

                with smt.push_solver(solver):
                    solver.add_assertion(smt.Not(smt.Equals(
                        lhs.interpret(canonical_structure, free_var_map_to_constants),
                        rhs.interpret(canonical_structure, free_var_map_to_constants)
                    )))

                    if not solver.solve():
                        dependent = check_equation_implication(found_axioms, equality, **vampire_args)

                        if not dependent:
                            print(f"\33[2K\r{equality}")
                            found_axioms.append(equality)

    print("\33[2K\r", end="")

    print(f"enumeration took {time.time() - start}s")
    print()
    start = time.time()

    # prune dependent axioms
    final_axioms = remove_dependent_axioms(found_axioms, **vampire_args)

    print(f"dependence check took {time.time() - start}s")
    print()

    return final_axioms


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--vampire", default="vampire", help="path to the vampire binary")
    args = parser.parse_args()

    re_model = FOModelTemplate(Parser.parse_theory(r"""
    theory REGULAR-LANGUAGE
        sort KA [smt("RegLan")]

        constant a: KA [smt("(str.to_re \"a\")")]
        constant b: KA [smt("(str.to_re \"b\")")]
        constant c: KA [smt("(str.to_re \"c\")")]

        constant zero: KA [smt("(re.none)")] // empty language
        constant one: KA [smt("(str.to_re \"\")")] // singleton language with an empty string
        function union: KA KA -> KA [smt("(re.union #1 #2)")]
        function concat: KA KA -> KA [smt("(re.++ #1 #2)")]
        function closure: KA -> KA [smt("(re.* #1)")]
    end
    """))

    ka_sort = re_model.language.get_sort("KA")

    c2d2_language = re_model.language.get_sublanguage(
        ("KA",),
        ("union", "concat", "closure", "one", "zero"),
        (),
    )

    c3d2_language = re_model.language.get_sublanguage(
        ("KA",),
        ("union", "concat", "closure"),
        (),
    )

    c2d2_equalities = find_axioms(
        c2d2_language, ka_sort, re_model, 1, 1,
        (Variable("a", ka_sort), Variable("b", ka_sort)),
        (
            re_model.language.get_function_symbol("a"),
            re_model.language.get_function_symbol("b"),
        ),
        (),
        vampire_binary=args.vampire,
    )
    final_axioms = find_axioms(
        c3d2_language, ka_sort, re_model, 2, 2,
        (Variable("a", ka_sort), Variable("b", ka_sort), Variable("c", ka_sort)),
        (
            re_model.language.get_function_symbol("a"),
            re_model.language.get_function_symbol("b"),
            re_model.language.get_function_symbol("c"),
        ),
        c2d2_equalities,
        vampire_binary=args.vampire,
    )

    print("final axioms:")
    for axiom in final_axioms:
        print(axiom)


if __name__ == "__main__":
    main()
