from typing import Mapping, Tuple, Dict

import z3
import itertools
import json

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.utils import FOLUtils

# terms = FOLUtils.get_ground_terms_in_language(theory_map["BTREE"].language, 3)

# for sort in terms:
#     print(sort)
#     for term in terms[sort]:
#         print("   ", term)

# test if term1 is a subterm of term2
def is_subterm(term1: Term, term2: Term) -> bool:
    if isinstance(term2, Variable):
        return term1 == term2

    if isinstance(term2, Application):
        if term1 == term2: return True

        for argument in term2.arguments:
            if is_subterm(term1, argument):
                return True

    return False

# build a prefix term model, with subterm relation(s)
def build_prefix_term_model(language: Language, depth: int) -> Structure:
    indices_to_terms = {
        sort: list(terms)
        for sort, terms in
        FOLUtils.get_ground_terms_in_language(language, depth).items()
    }

    terms_to_indices = {
        sort: { term: i for i, term in enumerate(terms) }
        for sort, terms in indices_to_terms.items()
    }

    carriers: Dict[Sort, CarrierSet] = {}
    function_interpretations: Dict[FunctionSymbol, smt.SMTFunction] = {}
    relation_interpretations: Dict[RelationSymbol, smt.SMTFunction] = {}

    for sort, terms in indices_to_terms.items():
        print(sort, len(terms))

    # build interpretations for functions
    for function_symbol in language.function_symbols:
        if function_symbol.smt_hook is not None:
            continue

        template = smt.Int(-1) # poison value
        placeholders = tuple(smt.FreshSymbol(smt.INT) for _ in function_symbol.input_sorts)

        if function_symbol.name.startswith("proj"):
            # destructor
            # TODO: hacky
            destructor_index = int(function_symbol.name[-1])
            constructor_name = function_symbol.name[len("proj"):-1].lower()
            placeholder, = placeholders
            input_sort, = function_symbol.input_sorts

            for term in indices_to_terms[input_sort]:
                assert isinstance(term, Application)

                if term.function_symbol.name.lower() == constructor_name:
                    assert destructor_index <= len(term.arguments)

                    value = terms_to_indices[input_sort][term]
                    result_term = term.arguments[destructor_index - 1]
                    result_value = terms_to_indices[function_symbol.output_sort][result_term]

                    template = smt.Ite(
                        smt.Equals(placeholder, smt.Int(value)),
                        smt.Int(result_value),
                        template,
                    )
        else:
            domains = tuple(list(range(len(indices_to_terms[sort]))) for sort in function_symbol.input_sorts)

            for values in itertools.product(*domains):
                corresponding_terms = tuple(indices_to_terms[sort][value] for sort, value in zip(function_symbol.input_sorts, values))

                result_term = Application(function_symbol, corresponding_terms)

                # out of bound of the partial model
                if result_term not in terms_to_indices[function_symbol.output_sort]:
                    continue

                result_value = terms_to_indices[function_symbol.output_sort][result_term]

                template = smt.Ite(
                    smt.And(smt.Equals(placeholder, smt.Int(value)) for placeholder, value in zip(placeholders, values)),
                    smt.Int(result_value),
                    template,
                )

        function_interpretations[function_symbol] = (lambda template, placeholders: lambda *args:
            template.substitute(dict(zip(placeholders, args)))
        )(template, placeholders)

    # build interpretations for subterm relations
    # NOTE: these are "partial" relations, it can evaluate to either 1 (true), 0 (false), or -1 (unknown)
    for relation_symbol in language.relation_symbols:
        if relation_symbol.smt_hook is not None:
            continue

        assert relation_symbol.name.startswith("sub") and len(relation_symbol.input_sorts) == 2, \
               "not a subterm relation"

        template = smt.TRUE()

        placeholders = tuple(smt.FreshSymbol(smt.INT) for _ in relation_symbol.input_sorts)
        domains = tuple(list(range(len(indices_to_terms[sort]))) for sort in relation_symbol.input_sorts)

        for values in itertools.product(*domains):
            term1, term2 = tuple(indices_to_terms[sort][value] for sort, value in zip(relation_symbol.input_sorts, values))

            template = smt.Ite(
                smt.And(smt.Equals(placeholder, smt.Int(value)) for placeholder, value in zip(placeholders, values)),
                smt.Bool(is_subterm(term1, term2) and term1 != term2),
                template,
            )

        relation_interpretations[relation_symbol] = (lambda template, placeholders: lambda *args:
            template.substitute(dict(zip(placeholders, args)))
        )(template, placeholders)

    for sort, terms in indices_to_terms.items():
        carriers[sort] = FiniteCarrierSet(smt.INT, tuple(smt.Int(i) for i in range(len(terms))))

    return SymbolicStructure(language, carriers, function_interpretations, relation_interpretations)


####################################### synthesis

theory_map = Parser.parse_theories(r"""
theory BTREE
    sort BTree
    constant c1: BTree
    constant c2: BTree
    function node: BTree BTree -> BTree
    function projNode1: BTree -> BTree
    function projNode2: BTree -> BTree
    relation eqBTree: BTree BTree [smt("(= #1 #2)")]
end
""")

btree_sort = theory_map["BTREE"].language.get_sort("BTree")

language = theory_map["BTREE"].language
prefix_model = build_prefix_term_model(language, 3)

print("model generated")

with smt.Solver(name="z3") as solver:
    # nat_x = Variable("x", nat_sort)
    # nat_y = Variable("y", nat_sort)
    # nat_z = Variable("z", nat_sort)

    btree_tx = Variable("tx", btree_sort)
    btree_ty = Variable("ty", btree_sort)
    btree_tz = Variable("tz", btree_sort)
    btree_tw = Variable("tw", btree_sort)

    free_vars = btree_tx, btree_ty, btree_tz, btree_tw
    fresh_sort = smt.FreshSort()

    # fix a free var assignment for triviality constraints
    free_var_assignment = {
        free_var: smt.FreshSymbol(fresh_sort)
        for free_var in free_vars
    }

    precomputed_instantiation_terms = FOLUtils.get_ground_terms_in_language(language, 2, free_vars=free_vars)
    precomputed_ground_terms = FOLUtils.get_ground_terms_in_language(language, 2)

    templates = (
        # Negation(AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True)),
        QuantifierFreeFormulaTemplate(language, (btree_tx, btree_ty), 0, 1, allow_constant=True),
        QuantifierFreeFormulaTemplate(language, (btree_tx, btree_ty), 1, 1, allow_constant=True),
        QuantifierFreeFormulaTemplate(language, (btree_tx, btree_ty), 0, 2, allow_constant=True),
        # Negation(QuantifierFreeFormulaTemplate(language, (btree_tx, btree_ty), 0, 0, allow_constant=True)),
        # Negation(AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True)),
        # Negation(AtomicFormulaTemplate(language, (btree_tx, btree_ty), 1, allow_constant=True)),
        # Implication(
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True),
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True),
        # ),
        # Implication(
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 1, allow_constant=True),
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True),
        # ),
        # Implication(
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 1, allow_constant=True),
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 1, allow_constant=True),
        # ),
        # Implication(
        #     Conjunction.from_conjuncts(
        #         AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True),
        #         AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True),
        #     ),
        #     AtomicFormulaTemplate(language, (btree_tx, btree_ty), 0, allow_constant=True),
        # ),
        # AtomicFormulaTemplate(language, (btree_tx, btree_ty), 1, allow_constant=True),
    )

    trivial_model = UninterpretedStructureTemplate(language, default_sort=fresh_sort)
    solver.add_assertion(trivial_model.get_constraint())

    learned_formulas = []

    def add_formula_to_trivial_model(formula):
        # assert all instantiations to trivial_model
        # so that we can avoid duplicate equalities
        free_vars = tuple(formula.get_free_variables())
        # print("instance of", equality)

        for instantiation in itertools.product(*(tuple(precomputed_instantiation_terms[free_var.sort]) for free_var in free_vars)):
            instantiated_formula = formula.substitute(dict(zip(free_vars, instantiation)))
            # print(instantiated_formula)
            solver.add_assertion(instantiated_formula.interpret(trivial_model, free_var_assignment))

    for template in templates:
        with smt.push_solver(solver):
            solver.add_assertion(template.get_constraint())

            free_vars = tuple(template.get_free_variables())
            domains = tuple(precomputed_ground_terms[var.sort] for var in free_vars)

            # print(free_vars)
            # only make instantiations that do not go out of bound
            for assignment in itertools.product(*domains):
                # print(dict(zip(free_vars, assignment)))
                solver.add_assertion(template.substitute(dict(zip(free_vars, assignment))).interpret(prefix_model, {}))

            solver.add_assertion(smt.Not(template.interpret(trivial_model, free_var_assignment)))

            for formula in learned_formulas:
                add_formula_to_trivial_model(formula)

            while True:
                if not solver.solve():
                    print("### cannot find more formulas")
                    break
                else:
                    model = solver.get_model()
                    candidate = template.get_from_smt_model(model)

                    # convert constants to variables, by the theorem that
                    # the validity of KA equality is equivalent to the validity
                    # of the gound equality with variables replaced with constants
                    # candidate = Equality(constants_to_variables(candidate.left), constants_to_variables(candidate.right))
                    print(candidate)

                    learned_formulas.append(candidate)
                    add_formula_to_trivial_model(candidate)

