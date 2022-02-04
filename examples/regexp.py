from typing import Mapping, Tuple, Dict

import z3
import itertools
import json

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.utils import FOLUtils

z3_ctx = z3.Context()

ka_theory = Parser.parse_theory(r"""
theory KLEENE-ALGEBRA
    sort KA
    relation eq: KA KA [smt("(= #1 #2)")]

    constant zero: KA // empty language
    constant one: KA // language with an empty word
    function union: KA KA -> KA
    function concat: KA KA -> KA
    function closure: KA -> KA
end
""")

ka_sort = ka_theory.language.get_sort("KA")


def encode_regex_in_z3(term: Term) -> z3.AstRef:
    if isinstance(term, Variable):
        # print("v", z3_ctx)
        return z3.Re(term.name, ctx=z3_ctx)

    elif isinstance(term, Application):
        # print("c", z3_ctx)
        arguments = tuple(encode_regex_in_z3(argument) for argument in term.arguments)
        z3_function = {
            "zero": lambda: z3.Empty(z3.ReSort(z3.StringSort(ctx=z3_ctx))),
            "one": lambda: z3.Re("", ctx=z3_ctx),
            "union": z3.Union,
            "concat": z3.Concat,
            "closure": z3.Star,
        }[term.function_symbol.name]

        return z3_function(*arguments)

    assert False, f"unknown term {term}"


def check_regex_equivalence(term1: Term, term2: Term) -> bool:
    """
    Check if two regex (represented as terms in KLEENE-ALGEBRA, where letters are represented by variables)
    """
    solver = z3.Solver(ctx=z3_ctx)
    # print(encode_regex_in_z3(term1).sort(), encode_regex_in_z3(term2).sort())
    solver.add(z3.Distinct(encode_regex_in_z3(term1), encode_regex_in_z3(term2)))
    return solver.check() != z3.sat
 

def check_regex_equivalence_batch(term: Term, candidates: Tuple[Term, ...]) -> Optional[int]:
    """
    Check if <term> is equivalent to any of the candidates, if so return the index
    """
    global z3_ctx

    # z3._main_ctx = z3.Context()
    z3_ctx = z3.Context()
    solver = z3.Solver(ctx=z3_ctx)
    equiv_flags = tuple(z3.FreshBool(ctx=z3_ctx) for _ in candidates)
    index_var = z3.FreshInt(ctx=z3_ctx)

    # print(index_var, equiv)

    # encoded_term = encode_regex_in_z3(term)
    # encoded_term = encode_regex_in_z3(term)
    # print(term, encoded_term)

    # print(z3_ctx)
    encoded_term = encode_regex_in_z3(term)
    # print(encoded_term.ctx)

    for i, (equiv_flag, candidate) in enumerate(zip(equiv_flags, candidates)):
        # TODO: this weird indexing thing is to ensure that z3 actually tells us which one is equivalent
        # otherwise the booleans in the returned model may not be fully evaluated
        solver.add(z3.Implies(z3.And(
            equiv_flag,
            z3.And(*(z3.Not(other_flags) for other_flags in equiv_flags[:i]), z3_ctx),
            z3_ctx,
        ), index_var == i, z3_ctx))

        solver.add(equiv_flag == (encoded_term == encode_regex_in_z3(candidate)))

    solver.add(z3.Or(*equiv_flags, z3_ctx))
    result = solver.check()

    if result == z3.sat:
        model = solver.model()
        # print(model)
        # print(model[index_var].as_long())
        # print(tuple(z3.is_true(model[equiv_flag]) for i, equiv_flag in enumerate(equiv_flags)))
        # # print(model)
        # # for i, equiv_flag in enumerate(equiv_flags):
        # #     print(z3.simplify(model[equiv_flag]))
        # #     if not bool(model[equiv_flag]):
        # #         return i
        return model[index_var].as_long()
    else:
        assert result == z3.unsat
        return None


def generate_partial_model(language: Language, depth: int) -> Tuple[int, Dict]:
    """
    A partial model over an alphabet A is a subset of the free Kleene algebra over A
    such thta it only includes terms up to a given depth.
    Out-of-bound mappings throws an exception.
    """

    constructors = []

    # name -> map of the form { (rep_index, ...) -> rep_index }
    constructor_evaluations = {}

    # id (int) -> represented term
    representatives = []
    alphabet_index = 0

    for function_symbol in language.function_symbols:
        name = function_symbol.name

        if len(function_symbol.input_sorts) == 0:
            constructor_evaluations[name] = { "": len(representatives) }
            
            if name == "zero":
                representatives.append(Parser.parse_term(language, "zero()"))
            elif name == "one":
                representatives.append(Parser.parse_term(language, "one()"))
            else:
                assert len(name) == 1, "due to the weird encoding we have right now"
                representatives.append(Variable(name, ka_sort))
                alphabet_index += 1
        else:
            constructors.append(function_symbol)
            constructor_evaluations[name] = {}


    # main loop:
    # for each depth, construct new terms from the existing representatives
    # each time check with the rest to see if it's equivalent
    # otherwise add it to representatives

    prev_num_representatives = 0

    for i in range(depth):
        new_representatives = []

        for constructor in constructors:
            arity = len(constructor.input_sorts)
            assert arity != 0

            # print(constructor, len(last_new_representatives), len(representatives), len(new_representatives))

            for indexed_arguments in itertools.product(enumerate(representatives), repeat=arity):
                new_term = Application(constructor, tuple(arg for _, arg in indexed_arguments))
                rep_indices = tuple(index for index, _ in indexed_arguments)

                # at least one of them should be a new representative found in the last batch
                # otherwise we are enumerating an old term
                for rep_index in rep_indices:
                    if rep_index >= prev_num_representatives:
                        break
                else:
                    continue

                # print(f"checking {len(representatives) + len(new_representatives)} terms")
                # old_terms = tuple(representatives + list(rep for _, rep in new_representatives))
                # result_rep_index = check_regex_equivalence_batch(new_term, old_terms)

                # if result_rep_index is None:
                #     print(new_term)
                #     result_rep_index = len(representatives) + len(new_representatives)
                #     new_representatives.append((result_rep_index, new_term))

                for index, representative in enumerate(representatives + new_representatives):
                    if check_regex_equivalence(new_term, representative):
                        result_rep_index = index
                        break
                else:
                    print(new_term)
                    result_rep_index = len(representatives) + len(new_representatives)
                    new_representatives.append(new_term)

                constructor_evaluations[constructor.name][",".join(map(str, rep_indices))] = result_rep_index

        prev_num_representatives = len(representatives)
        representatives.extend(new_representatives)

        print(f"depth {i}, found {len(new_representatives)} new terms, total {len(representatives)} terms")

    return len(representatives), constructor_evaluations


def evaluate_value_map(value_map: Dict[str, int], *args: smt.SMTTerm) -> smt.SMTTerm:
    result = smt.Int(-1)

    for key, value in value_map.items():
        int_args = () if key == "" else tuple(map(smt.Int, map(int, key.split(","))))
        assert len(args) == len(int_args)

        result = smt.Ite(
            smt.And(smt.Equals(expected, arg) for expected, arg in zip(int_args, args)),
            smt.Int(value),
            result,
        )

    return result

    # for arg in args:
    #     assert arg.is_int_constant(), f"{arg} should be an Int constant"
    #     int_args.append(str(arg.constant_value()))

    # key = ",".join(int_args)
    # assert key in value_map, f"{key} out of bound of the partial model"

    # return smt.Int(value_map[key])


def create_model(language: Language, size: int, maps: Dict[str, Dict[str, int]]) -> Structure:
    carrier = FiniteCarrierSet(smt.INT, [ smt.Int(i) for i in range(size) ])

    # build function interpretations
    functions = {}

    for function_name, value_map in maps.items():
        try:
            function_symbol = language.get_function_symbol(function_name)
            functions[function_symbol] = (lambda value_map: lambda *args: evaluate_value_map(value_map, *args))(value_map)
        except: ...

    return SymbolicStructure(language, { ka_sort: carrier }, functions, {})


def constants_to_variables(term: Term) -> Term:
    """
    Change constants (other than zero and one) in the term to variables with the same name
    """
    if isinstance(term, Application):
        name = term.function_symbol.name
        if len(term.function_symbol.input_sorts) == 0 and name not in ("zero", "one"):
            return Variable(name, ka_sort)

        return Application(term.function_symbol, tuple(constants_to_variables(arg) for arg in term.arguments))

    return term


def remove_dependent_axioms(formulas: Tuple[Formula]) -> Tuple[Formula]:
    """
    Return an equivalent theory but with all formulas independent (i.e. not implying each other)
    """


# print(encode_regex_in_z3(Parser.parse_term(ka_theory.language, "union(x:KA, y:KA)")))

# print(check_regex_equivalence(
#     Parser.parse_term(ka_theory.language, "union(x:KA, y:KA)"),
#     Parser.parse_term(ka_theory.language, "union(y:KA, x:KA)"),
# ))

# print(check_regex_equivalence(
#     Parser.parse_term(ka_theory.language, "union(x:KA, closure(x:KA))"),
#     Parser.parse_term(ka_theory.language, "concat(x:KA, closure(x:KA))"),
# ))

# print(check_regex_equivalence(
#     Parser.parse_term(ka_theory.language, "zero()"),
#     Parser.parse_term(ka_theory.language, "one()"),
# ))

# print(check_regex_equivalence_batch(
#     Parser.parse_term(ka_theory.language, "union(b:KA, a:KA)"),
#     [
#         Parser.parse_term(ka_theory.language, "a:KA"),
#         Parser.parse_term(ka_theory.language, "b:KA"),
#         Parser.parse_term(ka_theory.language, "zero()"),
#         Parser.parse_term(ka_theory.language, "one()"),
#         Parser.parse_term(ka_theory.language, "union(a:KA, b:KA)"),
#         Parser.parse_term(ka_theory.language, "union(a:KA, one())"),
#     ]
# ))

# print(check_regex_equivalence_batch(
#     Parser.parse_term(ka_theory.language, "union(b:KA, a:KA)"),
#     [
#         Parser.parse_term(ka_theory.language, "a:KA"),
#         Parser.parse_term(ka_theory.language, "b:KA"),
#         Parser.parse_term(ka_theory.language, "zero()"),
#         Parser.parse_term(ka_theory.language, "one()"),
#         Parser.parse_term(ka_theory.language, "union(a:KA, b:KA)"),
#         Parser.parse_term(ka_theory.language, "union(a:KA, one())"),
#     ]
# ))

# expanded_language = ka_theory.language.get_sublanguage(
#     ("KA",),
#     ("union", "concat", "closure"),
#     ("eq",),
# ).expand_with_functions((
#     FunctionSymbol((), ka_sort, "a"),
#     FunctionSymbol((), ka_sort, "b"),
#     FunctionSymbol((), ka_sort, "c"),
# ))

expanded_language = ka_theory.language.get_sublanguage(
    ("KA",),
    ("union", "concat", "closure"), # , "zero", "one"),
    ("eq",),
).expand_with_functions((
    FunctionSymbol((), ka_sort, "a"),
    FunctionSymbol((), ka_sort, "b"),
    FunctionSymbol((), ka_sort, "c"),
))

# To generate the model, uncomment the following
# with open("model2.json", "w") as f:
#     json.dump(generate_partial_model(expanded_language, 2), f)
# exit()

with open("model-c3-d2.json") as f:
    size, value_map = json.load(f)
    canonical_partial_model = create_model(expanded_language, size, value_map)

with smt.Solver(name="z3") as solver:
    precomputed_instantiation_terms = tuple(FOLUtils.get_ground_terms_in_language(expanded_language, 2)[ka_sort])
    # for term in precomputed_instantiation_terms:
    #     print(term, end=" ")

    equality_templates = (
        Equality(TermTemplate(expanded_language, (), 1, ka_sort), TermTemplate(expanded_language, (), 1, ka_sort)),
        Equality(TermTemplate(expanded_language, (), 2, ka_sort), TermTemplate(expanded_language, (), 2, ka_sort)),
    )

    trivial_model = UninterpretedStructureTemplate(expanded_language)
    solver.add_assertion(trivial_model.get_constraint())

    learned_equalities = []

    def add_equality_to_trivial_model(equality):
        # assert all instantiations to trivial_model
        # so that we can avoid duplicate equalities
        free_vars = tuple(candidate.get_free_variables())

        # print("instance of", equality)

        for instantiation in itertools.product(precomputed_instantiation_terms, repeat=len(free_vars)):
            instantiated_equality = candidate.substitute(dict(zip(free_vars, instantiation)))
            # print(instantiated_equality)
            solver.add_assertion(instantiated_equality.interpret(trivial_model, {}))

    for equality_template in equality_templates:
        with smt.push_solver(solver):
            solver.add_assertion(equality_template.get_constraint())
            solver.add_assertion(equality_template.interpret(canonical_partial_model, {}))
            solver.add_assertion(smt.Not(equality_template.interpret(trivial_model, {})))

            for equality in learned_equalities:
                add_equality_to_trivial_model(equality)

            while True:
                if not solver.solve():
                    print("cannot find more equalities")
                    break
                else:
                    model = solver.get_model()
                    candidate = equality_template.get_from_smt_model(model)

                    # convert constants to variables, by the theorem that
                    # the validity of KA equality is equivalent to the validity
                    # of the gound equality with variables replaced with constants
                    candidate = Equality(constants_to_variables(candidate.left), constants_to_variables(candidate.right))
                    print(candidate)

                    learned_equalities.append(candidate)
                    add_equality_to_trivial_model(candidate)
