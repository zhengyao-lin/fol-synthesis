from typing import Dict

from fol import *
from fol.prover import NaturalProof

import sys
sys.setrecursionlimit(16000)


def get_lemma_template(
    theory: Theory,
    foreground_sort: Sort,
    lemma_language: Language,
    term_depth: int,
    formula_depth: int,
    additional_free_vars: int,
) -> Dict[RelationSymbol, Formula]:
    fixpoint_relation_symbols = []

    for sentence in theory.sentences:
        if isinstance(sentence, FixpointDefinition) and \
           sentence.relation_symbol in lemma_language.relation_symbols:
            fixpoint_relation_symbols.append(sentence.relation_symbol)

    templates: Dict[RelationSymbol, Formula] = {} # template for each fixpoint relation
    free_vars = tuple(Variable(f"x{i}", foreground_sort) for i in range(additional_free_vars))

    free_var_index = additional_free_vars

    for relation_symbol in fixpoint_relation_symbols:
        arguments = []

        for sort in relation_symbol.input_sorts:
            arguments.append(Variable(f"x{free_var_index}", sort))
            free_var_index += 1

        assert relation_symbol not in templates, \
               f"duplicate fixpoint definitions for relation {relation_symbol}"

        rhs: Formula = QuantifierFreeFormulaTemplate(lemma_language, tuple(arguments) + free_vars, term_depth, formula_depth)

        for var in free_vars[::-1]:
            rhs = UniversalQuantification(var, rhs)

        # template for the current relation:
        # R(x) -> phi(x) 
        templates[relation_symbol] = Implication(RelationApplication(relation_symbol, tuple(arguments)), rhs).quantify_all_free_variables()

    return templates


def substitute_relation_application(relation_symbol: RelationSymbol, substitute: Formula, free_vars: Tuple[Variable, ...], formula: Formula) -> Formula:
    """
    Substitute applications of a relation symbol R
    in a given formula with another formula

    e.g. for phi(x), R(c())[R <- phi] := phi(c())
    """

    if isinstance(formula, RelationApplication):
        if formula.relation_symbol != relation_symbol:
            return formula

        assert len(free_vars) == len(relation_symbol.input_sorts) == len(formula.arguments)
        return substitute.substitute(dict(zip(free_vars, formula.arguments)))

    elif isinstance(formula, Falsum) or isinstance(formula, Verum):
        return formula

    elif isinstance(formula, Conjunction) or \
         isinstance(formula, Disjunction) or \
         isinstance(formula, Implication) or \
         isinstance(formula, Equivalence):
        return type(formula)(
            substitute_relation_application(relation_symbol, substitute, free_vars, formula.left),
            substitute_relation_application(relation_symbol, substitute, free_vars, formula.right),
        )

    elif isinstance(formula, Negation):
        return Negation(substitute_relation_application(relation_symbol, substitute, free_vars, formula.formula))

    elif isinstance(formula, UniversalQuantification) or \
         isinstance(formula, ExistentialQuantification):
        return type(formula)(formula.variable, substitute_relation_application(relation_symbol, substitute, free_vars, formula.body))

    assert False, f"unsupported formula {formula}"


def get_induction_obligation(definition: FixpointDefinition, formula: Formula) -> Formula:
    """
    Given a (closed) formlua of the form
    forall x. R(x) -> phi(x)

    and the fixpoint definition of R(x) <-> rho_R(x)

    return a formula
    forall x. rho_R(x; R <- phi) -> phi(x)
    (i.e. the hypothesis in Park induction)

    This works for both concrete formulas and templates
    """

    body = formula.strip_universal_quantifiers()
    assert isinstance(body, Implication)
    assert isinstance(body.left, RelationApplication)
    assert body.left.relation_symbol == definition.relation_symbol

    free_vars = []
    for argument in body.left.arguments:
        assert isinstance(argument, Variable)
        free_vars.append(argument)

    ind_hyp = body.right

    # rho_R(x; R <- phi)
    rho_of_phi = substitute_relation_application(
        definition.relation_symbol,
        ind_hyp, tuple(free_vars),
        # replace the variables in the original definition with the new variables first
        definition.definition.substitute(dict(zip(definition.variables, free_vars))),
    )

    return Implication(rho_of_phi, ind_hyp).quantify_all_free_variables()


def get_pfp(theory: Theory, formula: Formula) -> Formula:
    body = formula.strip_universal_quantifiers()
    assert isinstance(body, Implication)
    assert isinstance(body.left, RelationApplication)

    definition = theory.find_fixpoint_definition(body.left.relation_symbol)
    assert definition is not None

    return get_induction_obligation(definition, formula)


def check_validity(theory: Theory, foreground_sort: Sort, goal: Formula, depth: int) -> Tuple[bool, Language, Set[Formula]]:
    """
    Return if the goal is FO-provable under the given theory
    """
    with smt.Solver(name="z3") as solver:
        extended_language, conjuncts = NaturalProof.encode_validity(theory, foreground_sort, goal, depth)
        model = UninterpretedModelTemplate(extended_language)

        solver.add_assertion(model.get_constraint())

        for conjunct in conjuncts:
            solver.add_assertion(conjunct.interpret(model, {}))

        return not solver.solve(), extended_language, conjuncts # unsat -> valid or sat -> unprovable


def generate_finite_example(theory: Theory, foreground_sort: Sort, formulas: Iterable[Formula], lfp: bool = False, max_model_size: Optional[int] = None) -> Optional[Structure]:
    """
    Generate a finite model of theory such that the given formulas hold together with the theory
    """
    model_size = max_model_size or 5

    while True:
        with smt.Solver(name="z3") as solver:
            if lfp:
                finite_model: ModelTemplate = FiniteLFPModelTemplate(theory, { foreground_sort: model_size })
            else:
                finite_model = FiniteFOModelTemplate(theory, { foreground_sort: model_size })

            solver.add_assertion(finite_model.get_constraint())

            for formula in formulas:
                solver.add_assertion(formula.interpret(finite_model, {}))

            if solver.solve():
                return finite_model.get_from_smt_model(solver.get_model())

        if max_model_size is not None:
            return None

        # try again with larger size
        model_size += 1


def fossil(
    theory: Theory,
    foreground_sort: Sort,
    lemma_language: Language,
    goal: Formula,
    natural_proof_depth: int,
    lemma_term_depth: int,
    lemma_formula_depth: int,
    true_counterexample_size_bound: int,
    additional_free_vars: int = 0, # additional number of free variables (universally quantified) that can appear on the RHS of each lemma
) -> bool:
    """
    The FOSSIL algorithm with all three types of counterexamples
    """

    lemmas: List[Formula] = []
    lemma_templates = get_lemma_template(theory, foreground_sort, lemma_language, lemma_term_depth, lemma_formula_depth, additional_free_vars)
    lemma_union_template = UnionFormulaTemplate(*lemma_templates.values()) # union of all lemma templates for each relation

    type2_models: List[Structure] = []
    # type3_models: List[Tuple[Structure, RelationSymbol]] = []

    with smt.Solver(name="z3") as synth_solver:
        synth_solver.add_assertion(lemma_union_template.get_constraint())

        # the lemma should not be approximately FO provable
        fo_provable_counterexample = FOProvableModelTemplate(theory, unfold_depth=2)
        synth_solver.add_assertion(fo_provable_counterexample.get_constraint())
        synth_solver.add_assertion(smt.Not(lemma_union_template.interpret(fo_provable_counterexample, {})))

        while True:
            validity, extended_language, conjuncts = check_validity(theory.extend_axioms(lemmas), foreground_sort, goal, natural_proof_depth)

            if validity:
                print(f"{goal} is valid")
                return True

            print(f"{goal} is unprovable with lemmas:")
            for lemma in lemmas:
                print(f"- {lemma}")

            type1_model = generate_finite_example(Theory(extended_language, ()), foreground_sort, conjuncts)
            assert type1_model is not None

            print("*** found type 1 model")

            with smt.push_solver(synth_solver):

                # only type 2 models are accumulated across synthesis of different lemmas
                for type2_model in type2_models:
                    synth_solver.add_assertion(lemma_union_template.interpret(type2_model, {}))

                # try to synthesize a valid lemma
                while True:
                    with smt.push_solver(synth_solver):
                        synth_solver.add_assertion(smt.Not(lemma_union_template.interpret(type1_model, {})))
                        
                        if synth_solver.solve():
                            # obtaint a concrete lemma
                            lemma = lemma_union_template.get_from_smt_model(synth_solver.get_model())
                        else:
                            print("### lemmas are exhausted")
                            return False
                    
                    print(f"synthesized lemma {lemma}")

                    # check if the PFP of the lemma is FO-valid under the theory and other lemmas
                    # TODO: check the types
                    lemma_pfp = get_pfp(theory, lemma)
                    print(lemma_pfp)

                    # sequential lemmas
                    validity, extended_language, conjuncts = check_validity(theory.extend_axioms(lemmas), foreground_sort, lemma_pfp, natural_proof_depth)

                    if validity:
                        # valid lemma, add it to the list
                        print(f" - lemma is valid")
                        lemmas.append(lemma)
                        break
                    else:
                        synth_solver.add_assertion(smt.Not(lemma_union_template.equals(lemma)))
                        print(f" - lemma is not valid, generating counterexamples")

                    # unprovable lemma, either get a finite LFP model or finite FO model to refute it
                    type2_model = generate_finite_example(theory, foreground_sort, (Negation(lemma),), lfp=True, max_model_size=true_counterexample_size_bound)
                    if type2_model is not None:
                        print("*** found type 2 model")
                        synth_solver.add_assertion(lemma_union_template.interpret(type2_model, {}))
                        type2_models.append(type2_model)

                    else:
                        print("*** type 2 model not found, finding type 3 model")
                        # no bounded LFP model found
                        type3_model = generate_finite_example(Theory(extended_language, ()), foreground_sort, conjuncts)
                        assert type3_model is not None

                        print("*** found type 3 model")

                        relation_symbol = lemma.strip_universal_quantifiers().left.relation_symbol
                        pfp = get_pfp(theory, lemma_templates[relation_symbol])
                        synth_solver.add_assertion(pfp.interpret(type3_model, {}))


theory = Parser.parse_theory(r"""
theory LIST
    sort Pointer

    constant nil: Pointer
    function n: Pointer -> Pointer

    relation list: Pointer
    relation lseg: Pointer Pointer
    relation in_lseg: Pointer Pointer Pointer

    relation eq: Pointer Pointer [smt("(= #1 #2)")]

    fixpoint in_lseg(x, y, z) = not eq(y, z) /\ (eq(x, y) \/ in_lseg(x, n(y), z))
    fixpoint list(x) = eq(x, nil()) \/ (list(n(x)) /\ not in_lseg(x, n(x), nil()))
    fixpoint lseg(x, y) = eq(x, y) \/ (lseg(n(x), y) /\ not in_lseg(x, n(x), y))
end
""")

sort_pointer = theory.language.get_sort("Pointer")
assert sort_pointer is not None

# fossil(
#     theory,
#     sort_pointer,
#     theory.language.get_sublanguage(
#         ("Pointer",),
#         ("nil", "n"),
#         ("list", "lseg"),
#     ),
#     Parser.parse_formula(theory.language, f"forall x: Pointer. list(x) -> lseg(x, nil())"),
#     natural_proof_depth=1,
#     lemma_term_depth=0,
#     lemma_formula_depth=0,
#     true_counterexample_size_bound=6,
# )

# fossil(
#     theory,
#     sort_pointer,
#     theory.language.get_sublanguage(
#         ("Pointer",),
#         ("nil", "n"),
#         ("list", "lseg", "eq"),
#     ),
#     Parser.parse_formula(theory.language, f"forall x: Pointer. lseg(x, nil()) -> list(x)"),
#     natural_proof_depth=1,
#     lemma_term_depth=0,
#     lemma_formula_depth=1,
#     true_counterexample_size_bound=6,
# )

# fossil(
#     theory,
#     sort_pointer,
#     theory.language.get_sublanguage(
#         ("Pointer",),
#         ("nil", "n"),
#         ("list", "lseg", "in_lseg"),
#     ),
#     Parser.parse_formula(theory.language, r"forall x: Pointer, y: Pointer, z: Pointer. lseg(x, y) /\ lseg(y, z) -> not in_lseg(x, n(x), z)"),
#     natural_proof_depth=1,
#     lemma_term_depth=0,
#     lemma_formula_depth=2,
#     true_counterexample_size_bound=5,
#     additional_free_vars=1,
# )

# fossil(
#     theory,
#     sort_pointer,
#     theory.language.get_sublanguage(
#         ("Pointer",),
#         ("nil", "n"),
#         ("lseg", "in_lseg"),
#     ),
#     Parser.parse_formula(theory.language, r"forall x: Pointer, y: Pointer, z: Pointer. in_lseg(x, y, z) /\ lseg(y, z) -> lseg(x, z)"),
#     natural_proof_depth=1,
#     lemma_term_depth=0,
#     lemma_formula_depth=1,
#     true_counterexample_size_bound=5,
#     additional_free_vars=1,
# )


# 6 min
# fossil(
#     theory.remove_fixpoint_definition("list"),
#     sort_pointer,
#     theory.language.get_sublanguage(
#         ("Pointer",),
#         (),
#         ("lseg", "in_lseg"),
#     ),
#     Parser.parse_formula(theory.language, r"forall x: Pointer, y: Pointer, z: Pointer. in_lseg(x, y, z) /\ lseg(y, z) -> lseg(x, z)"),
#     natural_proof_depth=1,
#     lemma_term_depth=0,
#     lemma_formula_depth=1,
#     true_counterexample_size_bound=4,
#     additional_free_vars=0,
# )

# 4m57s
fossil(
    theory
      .remove_fixpoint_definition("list")
      .extend_axioms((
        # an extra lemma required
        Parser.parse_formula(theory.language, r"forall x: Pointer, y: Pointer, z: Pointer. in_lseg(x, y, z) /\ lseg(y, z) -> lseg(x, z)"),
    )),
    sort_pointer,
    theory.language.get_sublanguage(
        ("Pointer",),
        (),
        ("lseg",),
    ),
    Parser.parse_formula(theory.language, r"forall x: Pointer, y: Pointer, z: Pointer. lseg(x, y) /\ lseg(y, z) -> lseg(x, z)"),
    natural_proof_depth=2,
    lemma_term_depth=0,
    lemma_formula_depth=1,
    true_counterexample_size_bound=4,
    additional_free_vars=1,
)
