from __future__ import annotations

from typing import Mapping, Tuple, Dict, Generator
from dataclasses import dataclass

import z3
import os
import sys
import pickle
import itertools
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
    initial_axioms: Iterable[Equality] = (),
    solver_seed: int = 0,
) -> Tuple[Equality, ...]:
    constants = tuple(language.get_function_symbol(name) for name in constant_names)
    new_axioms: List[Equality] = []

    with smt.Solver(name="z3", random_seed=solver_seed) as synthesis_solver:
        left_term_template = TermTemplate(language, (), term_depth, sort=primary_sort)
        synthesis_solver.add_assertion(left_term_template.get_constraint())

        right_term_template = TermTemplate(language, (), term_depth, sort=primary_sort)
        synthesis_solver.add_assertion(right_term_template.get_constraint())

        # trivial_model is used for independence constraints
        trivial_model = UninterpretedStructureTemplate(language)
        synthesis_solver.add_assertion(trivial_model.get_constraint())

        # the axiom should not be trivially true
        synthesis_solver.add_assertion(smt.Not(smt.Equals(
            left_term_template.interpret(trivial_model, {}),
            right_term_template.interpret(trivial_model, {}),
        )))

        # precompute all terms needed for instantiation
        # instantiation_terms = tuple(
        #     term for _, term in
        #     TermTemplate(language, (), instantiation_depth, sort=primary_sort).enumerate()
        # )
        instantiation_terms = tuple(partial_structure.data.index_to_term[primary_sort])

        # term_template is true on partial_structure (and not undefined)
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

        print(f"# start synthesis for depth {term_depth}, instantiation size {len(instantiation_terms)}")

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

            print(f"found axiom {axiom}")

            axioms_to_add.append(axiom)
            new_axioms.append(axiom)

    return new_axioms


# def check_fo_implication(
#     instantiation_terms: Iterable[Term],
#     axioms: Iterable[Equality],
#     goal: Equality,
#     solver_seed: int = 0,
# ) -> Tuple[Equality, ...]:
#     """
#     Check if
#     """



def main():
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


    # save language as above but binds every function to the canonical model
    re_model = FOModelTemplate(Parser.parse_theory(r"""
    theory REGULAR-LANGUAGE
        sort KA [smt("RegLan")]

        constant a: KA [smt("(str.to_re \"a\")")]
        constant b: KA [smt("(str.to_re \"b\")")]
        constant c: KA [smt("(str.to_re \"c\")")]

        // constant zero: KA [smt("(re.none)")] // empty language
        // constant one: KA [smt("(str.to_re \"\")")] // singleton language with an empty string
        function union: KA KA -> KA [smt("(re.union #1 #2)")]
        function concat: KA KA -> KA [smt("(re.++ #1 #2)")]
        function closure: KA -> KA [smt("(re.* #1)")]
    end
    """))

    ka_sort = ka_theory.language.get_sort("KA")

    # "c2d2" = partial-kleene-constant-2-depth-2-full.pickle
    # "c3d2" = partial-kleene-constant-3-depth-2-reduced.pickle

    c2d2_data = FinitePartialStructureData.from_save_file("results/partial-kleene-constant-2-depth-2-full.pickle")
    c2d2 = FinitePartialStructure(c2d2_data)

    c3d2_data = FinitePartialStructureData.from_save_file("results/partial-kleene-constant-3-depth-2-reduced.pickle")
    c3d2 = FinitePartialStructure(c3d2_data)

    axioms: List[Equality] = []

    # term depth 1, using c2d2
    axioms.extend(synthesize_equations_from_partial_model(
        c2d2.language,
        ka_sort,
        ("a", "b"),
        1,
        c2d2,
        initial_axioms=axioms,
    ))

    # # term depth 2, using c2d2
    # axioms.extend(synthesize_equations_from_partial_model(
    #     c2d2.language,
    #     ka_sort,
    #     ("a", "b"),
    #     2,
    #     c2d2,
    #     initial_axioms=axioms,
    # ))

    # # term depth 2, using c3d2
    # axioms.extend(synthesize_equations_from_partial_model(
    #     c2d2.language,
    #     ka_sort,
    #     ("a", "b", "c"),
    #     2,
    #     c2d2,
    #     initial_axioms=axioms,
    # ))

# term1 = Parser.parse_term(re_model.language, "concat(a(), closure(concat(a(), one())))")
# term2 = Parser.parse_term(re_model.language, "concat(closure(union(union(a(), a()), zero())), b())")

# with smt.Solver(name="z3") as solver:
#     solver.add_assertion(smt.Equals(term1.interpret(re_model, {}), term2.interpret(re_model, {})))
#     print(solver.solve())

if __name__ == "__main__":
    main()
