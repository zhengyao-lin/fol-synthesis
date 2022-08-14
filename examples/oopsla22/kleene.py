from __future__ import annotations

from typing import Mapping, Tuple, Dict, Generator
from dataclasses import dataclass
from enum import Enum

import z3
import os
import re
import sys
import shutil
import pickle
import tempfile
import argparse
import itertools
import subprocess
import multiprocessing

from synthesis import *
from synthesis.fol.cegis import CEGISynthesizer
from synthesis.fol.utils import FOLUtils
from synthesis.utils.stopwatch import Stopwatch


@dataclass
class FinitePartialStructureData:
    """
    Definition (partial structure):
    For simplicity, we define in the unsorted case.
    Given a language L and a structure S,
    a partial structure S' of S is an L-structure
    such that:
    - There exists a distinguished element u in the
        domain |S'| of S'. And |S'| \ { u } is a subset
        of |S|.
    - Any function f in L is such that
        * f^{S'}(a_1, ..., a_n) = u if any a_i = u
        * If f^{S'}(a_1, ..., a_n) = b and a_1, ..., a_n, b
        are not u, then f^{S}(a_1, ..., a_n) = b
    - Any relation R in L is such that R^{S'} agrees
        with R^{S} on |S'| \ { u }

    A q-free ground formula/term is said to be undefined
    in S', if any of its subterms evaluates to u in S'.
    """

    """
    A compact and serialized version of a finite partial structure
    to fascilitate storing the structure on the disk.

    This class builds a finite partial structure S' of any structure S
    such that |S'| \ {u} is the evaluations (in S) of all terms up to
    a certain depth.

    NOTE: smt overrides are ignored in the language
    """

    language: Language
    term_depth: int

    index_to_term: Dict[Sort, List[Term]]
    term_to_index: Dict[Term, int]

    function_mappings: Dict[FunctionSymbol, Mapping[Tuple[int, ...], int]]
    relation_domains: Dict[RelationSymbol, Tuple[Tuple[int, ...]]]

    @staticmethod
    def from_structure(language: Language, term_depth: int, base_structure: Structure) -> FinitePartialStructureData:
        """
        Extract a FinitePartialStructureData from the base_structure
        """

        data = FinitePartialStructureData(language, term_depth, {}, {}, {}, {})

        data.initialize_domains(base_structure)

        for function_symbol in language.function_symbols:
            data.initialize_function_mapping(function_symbol)

        for relation_symbol in language.relation_symbols:
            data.initialize_relation_domain(base_structure, relation_symbol)

        return data

    def initialize_domains(self, base_structure: Structure) -> None:
        # enumerate through and index all terms
        # the n-th unique element in the base structure
        # will be indexed (n - 1)
        term_count = 0

        with smt.Solver(name="z3") as solver:
            for sort, term in TermTemplate(self.language, (), self.term_depth).enumerate():
                if sort not in self.index_to_term:
                    self.index_to_term[sort] = []

                # check if the term is interpreted to the same element of any previous terms
                # if yes, label the term with the same index;
                # otherwise, we found a new unique elemtn and will create a new index
                
                term_count += 1
                print(f"\rfound {len(self.index_to_term[sort])}/{term_count} unique terms", end="")

                for i, other in enumerate(self.index_to_term[sort]):
                    with smt.push_solver(solver):
                        base_elem1 = term.interpret(base_structure, {})
                        base_elem2 = other.interpret(base_structure, {})

                        # print(base_elem1.to_smtlib(), base_elem2.to_smtlib())

                        solver.add_assertion(smt.Not(smt.Equals(base_elem1, base_elem2)))

                        if not solver.solve():
                            # equal elements in the base structure
                            self.term_to_index[term] = i
                            break
                else:
                    self.term_to_index[term] = len(self.index_to_term[sort])
                    self.index_to_term[sort].append(term)

            print()

    def initialize_function_mapping(self, symbol: FunctionSymbol) -> None:
        # product of the domains of argument sorts
        # no need to include the undefined value here
        domain = tuple(
            range(len(self.index_to_term.get(sort, [])))
            for sort in symbol.input_sorts
        )

        mapping: OrderedDict[Tuple[int, ...], int] = OrderedDict()

        for arguments in itertools.product(*domain):
            # construct the corresponding term
            new_term = Application(
                symbol,
                tuple(self.index_to_term[sort][argument] for argument, sort in zip(arguments, symbol.input_sorts)),
            )

            if new_term in self.term_to_index:
                mapping[arguments] = self.term_to_index[new_term]

        self.function_mappings[symbol] = mapping

    def initialize_relation_domain(self, base_structure: Structure, symbol: RelationSymbol) -> None:
        possible_arguments = tuple(
            range(len(self.index_to_term.get(sort, [])))
            for sort in symbol.input_sorts
        )

        domain: List[Tuple[int, ...]] = []

        with smt.Solver(name="z3") as solver:
            for arguments in itertools.product(*possible_arguments):
                # convert back to terms
                terms = tuple(
                    self.index_to_term[sort][argument]
                    for argument, sort in zip(arguments, symbol.input_sorts)
                )

                with smt.push_solver(solver):
                    solver.add_assertion(smt.Not(RelationApplication(symbol, terms).interpret(base_structure, {})))

                    if not solver.solve():
                        # the relation is true on the arguments
                        domain.append(arguments)

        self.relation_domains[symbol] = tuple(domain)

    def save(self, path: str) -> None:
        """
        Save the current structure to disk
        """

        with open(path, "wb") as save_file:
            # strip SMT hooks for serialization
            data = (
                self.language.strip_smt_hook(),
                self.term_depth,
                { k.strip_smt_hook(): [ t.strip_smt_hook() for t in v ] for k, v in self.index_to_term.items() },
                { k.strip_smt_hook(): v for k, v in self.term_to_index.items() },
                { k.strip_smt_hook(): v for k, v in self.function_mappings.items() },
                { k.strip_smt_hook(): v for k, v in self.relation_domains.items() },
            )

            pickle.dump(data, save_file)

    @staticmethod
    def from_save_file(path: str) -> FinitePartialStructureData:
        """
        Load a saved FinitePartialStructureData from disk
        """

        with open(path, "rb") as save_file:
            return FinitePartialStructureData(*pickle.load(save_file))

    def get_undefined_value(self, sort: Sort) -> smt.SMTTerm:
        return smt.Int(len(self.index_to_term.get(sort, [])))

    def get_carriers(self, sort: Sort) -> CarrierSet:
        return FiniteCarrierSet(
            smt.INT,
            tuple(smt.Int(i) for i in range(1 + len(self.index_to_term.get(sort, [])))),
        )

    def get_function_interpretation(self, symbol: FunctionSymbol) -> smt.SMTFunction:
        placeholders = tuple(smt.FreshSymbol(smt.INT) for _ in symbol.input_sorts)
        constraint: smt.SMTTerm = self.get_undefined_value(symbol.output_sort)

        for arguments, result in self.function_mappings[symbol].items():
            constraint = smt.Ite(
                smt.And(smt.Equals(var, smt.Int(value)) for var, value in zip(placeholders, arguments)),
                smt.Int(result),
                constraint,
            )

        return lambda *arguments: constraint.substitute(dict(zip(placeholders, arguments)))

    def get_relation_interpretation(self, symbol: RelationSymbol) -> smt.SMTFunction:
        placeholders = tuple(smt.FreshSymbol(smt.INT) for _ in symbol.input_sorts)
        constraint: smt.SMTTerm = smt.FALSE()

        for arguments in self.relation_domains[symbol]:
            constraint = smt.Or(
                smt.And(smt.Equals(var, smt.Int(value)) for var, value in zip(placeholders, arguments)),
                constraint,
            )

        return lambda *arguments: constraint.substitute(dict(zip(placeholders, arguments)))


class FinitePartialStructure(SymbolicStructure):
    """
    Create a SymbolicStructure based on FinitePartialStructureData
    """

    def __init__(self, data: FinitePartialStructureData):
        self.data = data

        carriers: Dict[Sort, CarrierSet] = {
            sort: data.get_carriers(sort)
            for sort in data.language.sorts
        }

        function_interpretations = {
            function_symbol: data.get_function_interpretation(function_symbol)
            for function_symbol in data.language.function_symbols
        }

        relation_interpretations = {
            relation_symbol: data.get_relation_interpretation(relation_symbol)
            for relation_symbol in data.language.relation_symbols
        }

        super().__init__(data.language, carriers, function_interpretations, relation_interpretations)


def replace_constants_with_variables(term: Term, targets: Tuple[FunctionSymbol, ...]) -> Term:
    """
    Replaces target constant symbols in the term with variables with the same name
    """
    if isinstance(term, Application):
        if term.function_symbol in targets:
            assert len(term.function_symbol.input_sorts) == 0, \
                   f"replacing non-constant {term}"
            return Variable(term.function_symbol.name, term.function_symbol.output_sort)

        return Application(
            term.function_symbol,
            tuple(replace_constants_with_variables(arg, targets) for arg in term.arguments),
        )

    return term


def synthesize_equations_from_partial_model(
    language: Language,
    primary_sort: Sort, # main sort
    constant_names: Iterable[str], # symbols in the partial structure representing variables
    term_depth: int,
    partial_structure: FinitePartialStructure,
    instantiation_depth: int = 1,
    use_enumeration: bool = False,
    initial_axioms: Iterable[Equality] = (),
    solver_seed: int = 0,
    stopwatch: Stopwatch = Stopwatch(),
) -> Tuple[Equality, ...]:
    constants = tuple(language.get_function_symbol(name) for name in constant_names)
    new_axioms: List[Equality] = []

    with smt.Solver(name="z3", random_seed=solver_seed) as synthesis_solver:
        left_term_template = TermTemplate(language, (), term_depth, sort=primary_sort)
        if not use_enumeration:
            synthesis_solver.add_assertion(left_term_template.get_constraint())

        right_term_template = TermTemplate(language, (), term_depth, sort=primary_sort)
        if not use_enumeration:
            synthesis_solver.add_assertion(right_term_template.get_constraint())

        # trivial_model is used for independence constraints
        trivial_model = UninterpretedStructureTemplate(language)
        if not use_enumeration:
            synthesis_solver.add_assertion(trivial_model.get_constraint())

        # the axiom should not be trivially true
        if not use_enumeration:
            synthesis_solver.add_assertion(smt.Not(smt.Equals(
                left_term_template.interpret(trivial_model, {}),
                right_term_template.interpret(trivial_model, {}),
            )))

        # precompute all terms needed for instantiation
        instantiation_terms = tuple(
            term for _, term in
            TermTemplate(language, (), instantiation_depth, sort=primary_sort).enumerate()
        )
        # instantiation_terms = tuple(partial_structure.data.index_to_term[primary_sort])

        # term_template is true on partial_structure (and not undefined)
        if not use_enumeration:
            left_term_template_interp = left_term_template.interpret(partial_structure, {})
            right_term_template_interp = right_term_template.interpret(partial_structure, {})
            synthesis_solver.add_assertion(smt.And(
                # the left term is not undefined
                smt.Not(smt.Equals(left_term_template_interp, partial_structure.data.get_undefined_value(primary_sort))),
                # no need to say that the right term is not undefined

                # and they are equal
                smt.Equals(right_term_template_interp, left_term_template_interp),
            ))

        axioms_to_add: List[Equality] = list(initial_axioms)

        print(f"term instantiation size {len(instantiation_terms)}")

        def term_generator() -> Generator[Tuple[Term, Term], None, None]:
            for _, term1 in left_term_template.enumerate():
                for _, term2 in right_term_template.enumerate():
                    yield term1, term2

        generator = term_generator()

        while True:
            # instantiate new and existing axioms on all possible terms in term_template
            # which adds constraints for independence
            for axiom in axioms_to_add:
                free_vars = tuple(axiom.get_free_variables())

                # print(f"adding {axiom} for independence")

                # NOTE: here we are assuming an unsorted scenario
                for instantiation in itertools.product(instantiation_terms, repeat=len(free_vars)):
                    instantiated_axiom = axiom.substitute(dict(zip(free_vars, instantiation)))
                    synthesis_solver.add_assertion(instantiated_axiom.interpret(trivial_model, {}))
            axioms_to_add = []

            if use_enumeration:
                try:
                    left_term, right_term = next(generator)

                    with smt.push_solver(synthesis_solver):
                        # check for independence and truth on the partial model
                        left_term_interp = left_term.interpret(partial_structure, {})
                        right_term_interp = right_term.interpret(partial_structure, {})
                        synthesis_solver.add_assertion(smt.And(
                            # the left term is not undefined
                            smt.Not(smt.Equals(left_term_interp, partial_structure.data.get_undefined_value(primary_sort))),
                            # no need to say that the right term is not undefined

                            # and they are equal
                            smt.Equals(left_term_interp, right_term_interp),
                        ))

                        synthesis_solver.add_assertion(smt.Not(smt.Equals(
                            left_term.interpret(trivial_model, {}),
                            right_term.interpret(trivial_model, {}),
                        )))

                        if not synthesis_solver.solve():
                            # dependent or unsound
                            print(f"\33[2K\rdiscarded axiom {left_term} = {right_term}", end="", flush=True)
                            continue

                except StopIteration:
                    break

            else:
                if not synthesis_solver.solve():
                    # no more equalities can be found
                    break

                model = synthesis_solver.get_model()
                left_term = left_term_template.get_from_smt_model(model)
                right_term = right_term_template.get_from_smt_model(model)

            # replace constant symbols representing variables in the partial model
            left_term = replace_constants_with_variables(left_term, constants)
            right_term = replace_constants_with_variables(right_term, constants)
            axiom = Equality(left_term, right_term)

            print(f"\33[2K\rfound axiom {axiom}")

            axioms_to_add.append(axiom)
            new_axioms.append(axiom)

    return new_axioms


def encode_term_in_tptp(term: Term) -> str:
    """
    Encode a term in TPTP format (used in Vampire)

    In particular, we need to
    - upper-case all variables
    - for constant symbols, remove empty parentheses (i.e. c() => c)

    TODO: if two variables have the same upper case, we will have a wrong formula
    """
    encoding = str(term)
    encoding = re.sub(r"([^\s,()]+):[^\s,()]+", lambda m: m.group(1).upper(), encoding)
    encoding = re.sub(r"\(\s*\)", "", encoding)
    return encoding


def encode_formula_in_tptp(formula: Formula, top_level: bool = True) -> str:
    """
    Encode a equality in TPTP format, universally quantifying all free variables
    """

    if isinstance(formula, Implication):
        body = f"({encode_formula_in_tptp(formula.left, False)} => {encode_formula_in_tptp(formula.right, False)})"

    elif isinstance(formula, Equality):
        body = f"{encode_term_in_tptp(formula.left)} = {encode_term_in_tptp(formula.right)}"
    
    else:
        # TODO: only supports implication and equality here
        assert False, f"unsupported formula {formula}"

    if top_level:
        free_vars = tuple(formula.get_free_variables())
        free_var_names = tuple(var.name.upper() for var in free_vars)

        if len(free_var_names) != 0:
            quantifier = f"! [{', '.join(free_var_names)}] : "
        else:
            quantifier = ""

        return f"{quantifier}{body}"

    else:
        return body


def encode_ka_term_in_latex(term: Term) -> str:
    """
    Encode a Kleene algebra term in LaTeX
    """

    # level of precedence of function symbols
    precedence = {
        "zero": 3,
        "one": 3,
        "closure": 2,
        "concat": 1,
        "union": 0,
    }

    def should_parenthesize(subterm: Term) -> bool:
        if isinstance(subterm, Variable):
            return False
        
        assert isinstance(subterm, Application)

        # we should parenthesize a subterm if the top level function
        # it applies has smaller precedence
        return precedence[subterm.function_symbol.name] <= \
               precedence[term.function_symbol.name]

    def encode_subterm(subterm: Term) -> str:
        encoding = encode_ka_term_in_latex(subterm)

        if should_parenthesize(subterm):
            return "(" + encoding + ")"

        return encoding

    if isinstance(term, Variable):
        return term.name

    assert isinstance(term, Application)

    if term.function_symbol.name == "zero":
        return "0"

    elif term.function_symbol.name == "one":
        return "1"

    elif term.function_symbol.name == "union":
        left = encode_subterm(term.arguments[0])
        right = encode_subterm(term.arguments[1])
        return f"{left} + {right}"

    elif term.function_symbol.name == "concat":
        left = encode_subterm(term.arguments[0])
        right = encode_subterm(term.arguments[1])
        return f"{left}{right}"

    elif term.function_symbol.name == "closure":
        return f"{encode_subterm(term.arguments[0])}^*"

    assert False, f"unknown term {term}"


class VampireResult(Enum):
    PROVABLE = 1
    COUNTEREXAMPLE = 2
    UNKNOWN = 3


def check_fo_implication_with_vampire(
    axioms: Iterable[Equality],
    goal: Equality,
    vampire_binary: str = "vampire",
    timeout: int = 300, # in seconds
    problem_file_path: Optional[str] = None, # specify that the problem should be saved to <save_file>,
                                             # and the output should be saved to <save_file>.out
) -> VampireResult:
    axiom_encodings = tuple(
        f"fof(axiom_{i}, axiom, {encode_formula_in_tptp(axiom)})."
        for i, axiom in enumerate(axioms)
    )

    goal_encoding = f"fof(goal, conjecture, {encode_formula_in_tptp(goal)})."

    save_output = problem_file_path is not None

    if problem_file_path is None:
        ctx = tempfile.NamedTemporaryFile("w", suffix=".p")
        problem_file_path = ctx.name
    else:
        ctx = open(problem_file_path, "w")

    with ctx as problem_file:
        problem_file.write("\n".join(axiom_encodings) + "\n\n" + goal_encoding + "\n")
        problem_file.flush()

        # print(open(problem_file.name).read())

        proc = subprocess.Popen([
            vampire_binary,
            "--mode", "casc_sat",
            "-t", str(timeout),
            problem_file_path,
        ], stdout=subprocess.PIPE)

        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            
        stdout = proc.stdout.read().decode()

        if save_output:
            with open(problem_file_path + ".out", "w") as problem_output:
                problem_output.write(stdout)

        matches = re.finditer(r"Termination reason: (.*)", stdout)
        termination_reasons = set(match.group(1) for match in matches)

        # print(termination_reasons)

        if "Satisfiable" in termination_reasons:
            return VampireResult.COUNTEREXAMPLE

        elif "Refutation" in termination_reasons:
            return VampireResult.PROVABLE
        
        elif termination_reasons <= { "Unknown", "Time limit" }:
            return VampireResult.UNKNOWN
        
        else:
            assert False, f"unknown vampire termination reason(s) {termination_reasons}"


def check_fo_implication(
    language: Language, # language for term instantiation
    primary_sort: Sort,
    axioms: Iterable[Equality],
    goal: Equality,
    instantiation_depth: int = 1,
    solver_seed: int = 0,
) -> bool:
    """
    Check if axioms |= goal in first-order logic

    Assume that all free variables in axioms and goal are of the sort primary_sort
    """

    with smt.Solver(name="z3", random_seed=solver_seed) as solver:
        model = UninterpretedStructureTemplate(language)
        solver.add_assertion(model.get_constraint())

        goal_free_vars = tuple(goal.get_free_variables())

        skolem_constants = {
            free_var: smt.FreshSymbol(model.get_smt_sort(free_var.sort))
            for free_var in goal_free_vars
        }

        # generate instantiation terms with the skolem constants
        instantiation_terms: Tuple[smt.SMTTerm, ...] = tuple(
            term.interpret(model, skolem_constants)
            for _, term in TermTemplate(language, goal_free_vars, instantiation_depth, sort=primary_sort).enumerate()
        )

        for axiom in axioms:
            free_vars = tuple(axiom.get_free_variables())
            
            for assignment in itertools.product(instantiation_terms, repeat=len(free_vars)):
                solver.add_assertion(axiom.interpret(model, dict(zip(free_vars, assignment))))

        solver.add_assertion(smt.Not(goal.interpret(model, skolem_constants)))

        # if sat, then not unknown (return False)
        # if unsat, then the implication is true
        return not solver.solve()


def prune_axioms(
    args: argparse.Namespace,
    language: Language,
    primary_sort: Sort,
    axioms: Iterable[Equality],
    **solver_args,
) -> Tuple[Equality, ...]:
    """
    Remove provably dependent axioms, then return the rest
    """

    unchecked_axioms = list(axioms)
    independent_axioms: List[Equality] = []

    while len(unchecked_axioms) != 0:
        # pop from the head since weaker axioms
        # are synthesized first
        axiom = unchecked_axioms.pop(0)

        if args.vampire_pruning:
            # use vampire to check implication
            result = check_fo_implication_with_vampire(
                unchecked_axioms + independent_axioms,
                axiom,
                vampire_binary=args.vampire,
                timeout=args.vampire_timeout,
            )

            if result != VampireResult.PROVABLE:
                print(f"checked axiom {axiom}")
                independent_axioms.append(axiom)
            else:
                print(f"pruned axiom {axiom}")

        else:
            if not check_fo_implication(
                language,
                primary_sort,
                unchecked_axioms + independent_axioms,
                axiom,
                **solver_args,
            ):
                print(f"checked axiom {axiom}")
                independent_axioms.append(axiom)
            else:
                print(f"pruned axiom {axiom}")

    return tuple(independent_axioms)


def compare_with_kozens(
    language: Language,
    axioms: Iterable[Formula],
    **vampire_args,
) -> None:
    """
    Compare the given set of axioms with Kozen's axioms of Kleene algebra
    And output the comparison results
    """

    axioms = tuple(axioms)

    kozens = tuple(map(lambda src: Parser.parse_formula(language, src), (
        "union(a:KA, union(b:KA, c:KA)) = union(union(a:KA, b:KA), c:KA)",
        "union(a:KA, b:KA) = union(b:KA, a:KA)",
        "union(a:KA, zero()) = a:KA",
        "union(a:KA, a:KA) = a:KA",
        "concat(a:KA, concat(b:KA, c:KA)) = concat(concat(a:KA, b:KA), c:KA)",
        "concat(one(), a:KA) = a:KA",
        "concat(a:KA, one()) = a:KA",
        "concat(a:KA, union(b:KA, c:KA)) = union(concat(a:KA, b:KA), concat(a:KA, c:KA))",
        "concat(union(a:KA, b:KA), c:KA) = union(concat(a:KA, c:KA), concat(b:KA, c:KA))",
        "concat(zero(), a:KA) = zero()",
        "concat(a:KA, zero()) = zero()",
        "union(union(one(), concat(a:KA, closure(a:KA))), closure(a:KA)) = closure(a:KA)",
        "union(union(one(), concat(closure(a:KA), a:KA)), closure(a:KA)) = closure(a:KA)",
        "(union(union(b:KA, concat(a:KA, x:KA)), x:KA) = x:KA -> union(concat(closure(a:KA), b:KA), x:KA) = x:KA)",
        "(union(union(b:KA, concat(x:KA, a:KA)), x:KA) = x:KA -> union(concat(b:KA, closure(a:KA)), x:KA) = x:KA)",
    )))

    # only (unconditional) equational axioms
    kozens_equational = kozens[:-2]

    # check if ours => kozen's equational axioms
    print("\n# checking if our axioms are stronger than Kozen's equational axioms")
    for i, kozen in enumerate(kozens_equational):
        print(f"axioms => {kozen}: ", end="", flush=True)
        result = check_fo_implication_with_vampire(axioms, kozen, problem_file_path=f"ours-to-kozen-{i}.p", **vampire_args)
        print(result)

    # check if kozen's equational axioms imply ours
    print("\n# checking if Kozen's equational axioms imply our axioms")
    not_implied: List[Tuple[int, Formula]] = [] # axioms not implied by Kozen's equational axioms
    for i, axiom in enumerate(axioms):
        print(f"equational kozens => {axiom}: ", end="", flush=True)
        result = check_fo_implication_with_vampire(kozens_equational, axiom, problem_file_path=f"kozens-equational-to-our-{i}.p", **vampire_args)
        print(result)

        if result != VampireResult.PROVABLE:
            not_implied.append((i, axiom))

    # check if all of Kozen's axioms imply ours
    print("\n# checking if all of Kozen's axioms imply our axioms")
    for i, axiom in not_implied:
        print(f"kozens => {axiom}: ", end="", flush=True)
        result = check_fo_implication_with_vampire(kozens, axiom, problem_file_path=f"kozens-to-our-{i}.p", **vampire_args)
        print(result)


def save_pickle(obj: Any, path: str) -> None:
    # pickle to a temporary file first in case pickling failed
    with tempfile.NamedTemporaryFile() as temp_file:
        pickle.dump(obj, temp_file)
        temp_file.flush()
        shutil.copy(temp_file.name, path)


def try_load_pickle(path: str) -> Any:
    """
    Return None if failed to unpickle, otherwise return the result of pickle.load
    """

    if not os.path.isfile(path):
        return None

    with open(path, "rb") as pickle_file:
        try:
            return pickle.load(pickle_file)
        except pickle.UnpicklingError:
            return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache", default=None, help="cache directory")
    parser.add_argument("--enumeration", action="store_true", default=False, help="use an enumerative synthesizer")
    parser.add_argument("--vampire", default="vampire", help="path to the Vampire binary")
    parser.add_argument("--vampire-timeout", type=int, default=300, help="timeout for pruning using Vampire, in seconds")
    parser.add_argument("--vampire-pruning", action="store_true", default=False, help="use Vampire for pruning")
    parser.add_argument("--vampire-save", action="store_true", default=False, help="save problems and results of Vampire")
    args = parser.parse_args()

    # prepare work directory
    if args.cache is None:
        args.cache = tempfile.mkdtemp()

    if not os.path.isdir(args.cache):
        os.mkdir(args.cache)

    os.chdir(args.cache)
    print(f"using cache directory {args.cache}")

    if os.path.isfile("stopwatch.pickle"):
        with open("stopwatch.pickle", "rb") as stopwatch_file:
            stopwatch = pickle.load(stopwatch_file)
    else:
        stopwatch = Stopwatch()

    ka_theory = Parser.parse_theory(r"""
    theory KLEENE-ALGEBRA
        sort KA
        // relation eq: KA KA [smt("(= #1 #2)")]

        constant zero: KA
        constant one: KA
        function union: KA KA -> KA
        function concat: KA KA -> KA
        function closure: KA -> KA
    end
    """)
    ka_sort = ka_theory.language.get_sort("KA")

    # save language as above but binds every function to the canonical model
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

    #############################
    # Define relevant languages #
    #############################

    full_language = re_model.language.strip_smt_hook()

    c2d1_language = re_model.language.get_sublanguage(
        ("KA",),
        ("a", "b", "zero", "one", "union", "concat", "closure"),
        (),
    )

    c2d2_language = c2d1_language

    c3d2_language = re_model.language.get_sublanguage(
        ("KA",),
        ("a", "b", "c", "union", "concat", "closure"),
        (),
    )

    # language used for pruning dependent axioms
    prune_language = full_language.get_sublanguage(
        ("KA",),
        ("a", "b", "zero", "one", "union", "concat", "closure"),
        (),
    )

    ######################################################
    # Specify the passes and the partial models required #
    ######################################################

    partial_model_specs = (
        ("c2d1", c2d1_language, 1, "partial-kleene-constant-2-depth-1-full.pickle"),
        ("c2d2", c2d2_language, 2, "partial-kleene-constant-2-depth-2-full.pickle"),
        ("c3d2", c3d2_language, 2, "partial-kleene-constant-3-depth-2-reduced.pickle"),
    )

    synthesis_parameters = (
        # term depth 1, using c2d2
        ("c2d1-depth-1", "c2d1", ("a", "b"), 1, "c2d1-depth-1.pickle"),

        # term depth 2, using c2d2
        ("c2d2-depth-2", "c2d2", ("a", "b"), 2, "c2d2-depth-2.pickle"),

        # term depth 2, using c3d2
        ("c3d2-depth-2", "c3d2", ("a", "b", "c"), 2, "c3d2-depth-2.pickle"),
    )

    # generate all required partial models (or load them from cache if exists)
    partial_models: Dict[str, FinitePartialStructure] = {}

    for name, language, term_depth, cache_file in partial_model_specs:
        # if cache exists, load the structure from cache
        if try_load_pickle(cache_file) is not None:
            print(f"\n# found cache for partial model {name}")
            data = FinitePartialStructureData.from_save_file(cache_file)
        else:
            print(f"\n# generating partial model {name}")
            with stopwatch.time(f"partial-model-generation-{name}", clear=True):
                data = FinitePartialStructureData.from_structure(language, term_depth, re_model)

            save_pickle(stopwatch, "stopwatch.pickle")
            data.save(cache_file)
        
        gen_time = stopwatch.get(f"partial-model-generation-{name}")
        print(f"- generating partial model {name} took {gen_time}s")

        partial_models[name] = FinitePartialStructure(data)

    axioms: List[Equality] = []
    new_axioms: List[Equality] = []
    num_previous_axioms = 0
    found_uncached = False

    def print_pass_stats(stopwatch: Stopwatch, pass_name: str) -> None:
        synthesis_time = stopwatch.get(f"synthesis-{pass_name}")
        pruning_time = stopwatch.get(f"pruning-{pass_name}")
        num_pruned_axioms = num_previous_axioms + len(new_axioms) - len(axioms)

        print(f"synthesized {len(new_axioms)} new axioms, pruned {num_pruned_axioms} axioms")
        print(f"- synthesis took {synthesis_time}s")
        print(f"- pruning took {pruning_time}s")

    # synthesis for each pass
    # NOTE: using cache, we can only start from the first uncached pass
    for pass_name, model_name, free_vars, term_depth, pass_cache_file in synthesis_parameters:
        num_previous_axioms = len(axioms)

        # try loading cache
        if not found_uncached:
            cached_pass = try_load_pickle(pass_cache_file)
            if cached_pass is None:
                found_uncached = True
            else:
                print(f"\n# found cache for pass {pass_name}")
                new_axioms, axioms = cached_pass
                print_pass_stats(stopwatch, pass_name)
                continue

        print(f"\n# starting synthesis for pass {pass_name}")

        partial_model = partial_models[model_name]

        with stopwatch.time(f"synthesis-{pass_name}", clear=True):
            new_axioms = synthesize_equations_from_partial_model(
                language=partial_model.language.strip_smt_hook(),
                primary_sort=ka_sort,
                constant_names=free_vars,
                term_depth=term_depth,
                partial_structure=partial_model,
                instantiation_depth=1,
                use_enumeration=args.enumeration,
                # only use axioms that are in the target language
                initial_axioms=tuple(axiom for axiom in axioms if axiom.is_in_language(partial_model.language)),
                stopwatch=stopwatch,
            )
            axioms.extend(new_axioms)

        # prune after each round
        with stopwatch.time(f"pruning-{pass_name}", clear=True):
            axioms = list(prune_axioms(args, prune_language, ka_sort, axioms))

        print_pass_stats(stopwatch, pass_name)

        save_pickle(stopwatch, "stopwatch.pickle")
        save_pickle((new_axioms, axioms), pass_cache_file)

    for axiom in axioms:
        print(f"final axiom {axiom}")

    print("\n# final axioms in LaTeX")
    print(r"\begin{enumerate}")
    for axiom in axioms:
        print(f"    \\item ${encode_ka_term_in_latex(axiom.left)} = {encode_ka_term_in_latex(axiom.right)}$")
    print(r"\end{enumerate}")

    compare_with_kozens(
        ka_theory.language,
        axioms,
        vampire_binary=args.vampire,
        timeout=args.vampire_timeout,
    )


if __name__ == "__main__":
    main()
