from typing import Generator, Set, Collection
from collections import OrderedDict

import itertools

from synthesis.utils.ordered import OrderedSet

from .base import *


class FOLUtils:
    @staticmethod
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

        elif isinstance(formula, Falsum) or isinstance(formula, Verum) or isinstance(formula, Equality):
            return formula

        elif isinstance(formula, Conjunction) or \
            isinstance(formula, Disjunction) or \
            isinstance(formula, Implication) or \
            isinstance(formula, Equivalence):
            return type(formula)(
                FOLUtils.substitute_relation_application(relation_symbol, substitute, free_vars, formula.left),
                FOLUtils.substitute_relation_application(relation_symbol, substitute, free_vars, formula.right),
            )

        elif isinstance(formula, Negation):
            return Negation(FOLUtils.substitute_relation_application(relation_symbol, substitute, free_vars, formula.formula))

        elif isinstance(formula, UniversalQuantification) or \
            isinstance(formula, ExistentialQuantification):
            return type(formula)(formula.variable, FOLUtils.substitute_relation_application(relation_symbol, substitute, free_vars, formula.body))

        assert False, f"unsupported formula {formula}"

    @staticmethod
    def get_ground_terms_in_language(language: Language, depth: int, free_vars: Tuple[Term, ...] = ()) -> Mapping[Sort, Collection[Term]]:
        """
        Depth 1 for constants
        Depth 2 for functions applied to constants
        ...
        """

        terms: OrderedDict[Sort, OrderedSet[Term]] = OrderedDict()
        new_terms: OrderedDict[Sort, OrderedSet[Term]] = OrderedDict()

        for current_depth in range(depth):
            if current_depth == 0:
                for free_var in free_vars:
                    if free_var.sort not in new_terms:
                        new_terms[free_var.sort] = OrderedSet()
                    new_terms[free_var.sort].add(free_var)

            for symbol in language.function_symbols:
                arg_combinations = tuple(terms.get(input_sort, OrderedSet()) for input_sort in symbol.input_sorts)

                for args in itertools.product(*arg_combinations):
                    new_term = Application(symbol, args)

                    if symbol.output_sort not in terms or \
                       new_term not in terms[symbol.output_sort]:
                        if symbol.output_sort not in new_terms:
                            new_terms[symbol.output_sort] = OrderedSet()

                        new_terms[symbol.output_sort].add(new_term)
                        # yield new_term

            # merge new_terms to terms
            for sort in new_terms:
                if sort not in terms:
                    terms[sort] = OrderedSet()
                terms[sort].update(new_terms[sort])
            new_terms = OrderedDict()

        return terms # type: ignore
