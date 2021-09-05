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
