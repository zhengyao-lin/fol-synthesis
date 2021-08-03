from __future__ import annotations

from typing import Tuple, Mapping, Callable, Optional, Dict

from fol.smt import smt
from fol.base.syntax import *

from .template import Template, BoundedIntegerVariable


class UnionFormulaTemplate(Formula):
    """
    A template whose value ranges in the union of all given templates
    """

    def __init__(self, *templates: Formula):
        assert len(templates) != 0
        self.node = BoundedIntegerVariable(0, len(templates))
        self.templates = tuple(templates)

    def get_free_variables(self) -> Set[Variable]:
        free_vars = set()

        for template in self.templates:
            free_vars.update(template.get_free_variables())

        return free_vars

    def substitute(self, substitution: Mapping[Variable, Term]) -> UnionFormulaTemplate:
        return UnionFormulaTemplate(*(template.substitute(substitution) for template in self.templates))

    def get_constraint(self) -> smt.SMTTerm:
        return smt.Or(*(
            smt.And(
                self.node.equals(index + 1),
                template.get_constraint()
            )
            for index, template in enumerate(self.templates)
        ))

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        node_value = self.node.get_from_smt_model(model)
        assert 1 <= node_value <= len(self.templates), \
               f"invalid node value {node_value}"

        return self.templates[node_value - 1].get_from_smt_model(model)

    def equals(self, value: Formula) -> smt.SMTTerm:
        return smt.Or(*(template.equals(value) for template in self.templates))

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        return smt.Or(*(
            smt.Ite(
                self.node.equals(index + 1),
                template.interpret(structure, valuation),
                smt.FALSE(),
            )
            for index, template in enumerate(self.templates)
        ))


class TermTemplate(Term):
    """
    Template for a term
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], depth: int, sort: Optional[Sort] = None):
        self.language = language
        self.free_vars = free_vars
        self.depth = depth
        self.sort = sort
        
        self.substitution: Dict[Variable, Term] = { var: var for var in self.free_vars }

        self.node = BoundedIntegerVariable(0, len(self.free_vars) + len(self.language.function_symbols))

        if depth != 0:
            self.subterms = tuple(TermTemplate(language, self.free_vars, depth - 1) for _ in range(language.get_max_function_arity()))
        else:
            self.subterms = ()

    def get_free_variables(self) -> Set[Variable]:
        free_vars = set()

        for var in self.free_vars:
            free_vars.update(self.substitution[var].get_free_variables())

        return free_vars

    def substitute(self, substitution: Mapping[Variable, Term]) -> TermTemplate:
        # TODO: check sorting
        new_template = TermTemplate(self.language, self.free_vars, self.depth, self.sort)
        new_template.substitution = { k: v.substitute(substitution) for k, v in self.substitution.items() }
        return new_template

    def get_constraint(self) -> smt.SMTTerm:
        """
        The term can be of any sort
        """
        return smt.Or(*(self.get_well_formedness_constraint(sort) for sort in self.language.sorts))

    def get_from_smt_model(self, model: smt.SMTModel) -> Term:
        """
        Get a concrete term from the given model
        """
        node_value = self.node.get_from_smt_model(model)
        assert node_value != 0, f"unexpected node value {node_value}"

        if node_value <= len(self.free_vars):
            return self.substitution[self.free_vars[node_value - 1]].get_from_smt_model(model)
        else:
            symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
            arity = len(symbol.input_sorts)
            return Application(symbol, tuple(subterm.get_from_smt_model(model) for subterm in self.subterms[:arity]))

    def equals(self, value: Term) -> smt.SMTTerm:
        constraint = smt.FALSE()

        for node_value in range(1, len(self.free_vars) + len(self.language.function_symbols) + 1):
            if node_value <= len(self.free_vars):
                variable = self.free_vars[node_value - 1]
                constraint = smt.Or(smt.And(self.node.equals(node_value), self.substitution[variable].equals(value)), constraint)
            elif isinstance(value, Application):
                symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
                arity = len(symbol.input_sorts)

                if value.function_symbol == symbol and (self.depth != 0 or arity == 0):
                    assert len(value.arguments) == arity

                    constraint = smt.Or(
                        smt.And(
                            self.node.equals(node_value),
                            *(subterm.equals(argument) for argument, subterm in zip(value.arguments, self.subterms[:arity])),
                        ),
                        constraint,
                    )

        return constraint

    def get_is_null_constraint(self) -> smt.SMTTerm:
        """
        Return a constraint saying that the subtree starting at self does not exist
        """
        return smt.And(self.node.equals(0), *(subterm.get_is_null_constraint() for subterm in self.subterms))

    def get_well_formedness_constraint(self, sort: Sort) -> smt.SMTTerm:
        """
        Return a constraint saying that the term is well-formed and has sort <sort> 
        """
        constraint = smt.FALSE()

        for node_value in range(1, len(self.free_vars) + len(self.language.function_symbols) + 1):
            if node_value <= len(self.free_vars):
                variable = self.free_vars[node_value - 1]

                if variable.sort == sort:
                    constraint = smt.Or(
                        smt.And(
                            self.node.equals(node_value),
                            self.substitution[variable].get_constraint(),
                            *(subterm.get_is_null_constraint() for subterm in self.subterms),
                        ),
                        constraint,
                    )
            else:
                symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
                arity = len(symbol.input_sorts)

                if symbol.output_sort == sort and (self.depth != 0 or arity == 0):
                    constraint = smt.Or(
                        smt.And(
                            self.node.equals(node_value),
                            # the i-th subterm should have the i-th input sort
                            *(subterm.get_well_formedness_constraint(sort) for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])),
                            *(subterm.get_is_null_constraint() for subterm in self.subterms[arity:]),
                        ),
                        constraint,
                    )

        return smt.And(constraint, self.node.get_constraint())

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        assert self.sort is not None, \
               f"term variable does not have a specific sort"
        return self.interpret_as_sort(self.sort, structure, valuation)

    def interpret_as_sort(self, sort: Sort, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        """
        Interpret the undetermined term in the given structure and valuation
        """

        carrier = structure.interpret_sort(sort)
        interp = smt.FreshSymbol(carrier.get_smt_sort())

        for node_value in range(1, len(self.free_vars) + len(self.language.function_symbols) + 1):
            if node_value <= len(self.free_vars):
                variable = self.free_vars[node_value - 1]
                if variable.sort == sort:
                    assert variable in valuation, f"unable to interpret variable {variable}"
                    interp = smt.Ite(self.node.equals(node_value), self.substitution[variable].interpret(structure, valuation), interp)

            else:
                symbol = self.language.function_symbols[node_value - len(self.free_vars) - 1]
                arity = len(symbol.input_sorts)

                if symbol.output_sort == sort and (self.depth != 0 or arity == 0):
                    arguments = tuple(
                        subterm.interpret_as_sort(subterm_sort, structure, valuation)
                        for subterm_sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])
                    )
                    interp = smt.Ite(self.node.equals(node_value), structure.interpret_function(symbol, *arguments), interp)

        return interp


class AtomicFormulaTemplate(Formula):
    """
    Template for an atomic formula (i.e. false, true, or other relations)
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], term_depth: int, allow_constant: bool = False):
        self.language = language
        self.term_depth = term_depth
        self.allow_constant = allow_constant # allow bottom and top
        self.node = BoundedIntegerVariable(0, 3 + len(language.relation_symbols))

        self.subterms = tuple(TermTemplate(language, free_vars, term_depth) for _ in range(language.get_max_relation_arity()))

    def __str__(self) -> str:
        return f"<φ({', '.join(map(str, self.get_free_variables()))}), depth {self.term_depth}>"

    def get_free_variables(self) -> Set[Variable]:
        free_vars = set()

        for subterm in self.subterms:
            free_vars.update(subterm.get_free_variables())

        return free_vars

    def substitute(self, substitution: Mapping[Variable, Term]) -> AtomicFormulaTemplate:
        new_formula = AtomicFormulaTemplate(self.language, (), self.term_depth, self.allow_constant)
        new_formula.subterms = tuple(subterm.substitute(substitution) for subterm in self.subterms)
        return new_formula

    def get_constraint(self) -> smt.SMTTerm:
        return self.get_well_formedness_constraint()

    def get_from_smt_model(self, model: smt.SMTModel) -> AtomicFormula:
        """
        Get a concrete atomic formula from the model
        """
        node_value = self.node.get_from_smt_model(model)

        if node_value == 1:
            return Falsum()
        elif node_value == 2:
            return Verum()
        else:
            symbol = self.language.relation_symbols[node_value - 3]
            arity = len(symbol.input_sorts)
            return RelationApplication(symbol, tuple(subterm.get_from_smt_model(model) for subterm in self.subterms[:arity]))

    def equals(self, value: Formula) -> smt.SMTTerm:
        """
        Return a constraint saying that the variable equals the given atomic formula
        """
        if isinstance(value, Falsum):
            return self.node.equals(1)

        elif isinstance(value, Verum):
            return self.node.equals(2)

        elif isinstance(value, RelationApplication) and \
             value.relation_symbol in self.language.relation_symbols:

            symbol_index = self.language.relation_symbols.index(value.relation_symbol)
            arity = len(value.relation_symbol.input_sorts)

            return smt.And(
                self.node.equals(symbol_index + 3),
                *(subterm.equals(argument) for argument, subterm in zip(value.arguments, self.subterms[:arity])),
            )

        else:
            return smt.FALSE()

    def get_is_null_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.node.equals(0),
            *(subterm.get_is_null_constraint() for subterm in self.subterms),
        )

    def get_well_formedness_constraint(self) -> smt.SMTTerm:
        constraint = smt.FALSE()

        for node_value in range(1, 3 + len(self.language.relation_symbols)):
            if node_value == 1 or node_value == 2:
                if self.allow_constant:
                    constraint = smt.Or(
                        smt.And(
                            self.node.equals(node_value),
                            *(subterm.get_is_null_constraint() for subterm in self.subterms),
                        ),
                        constraint,
                    )
            else:
                symbol = self.language.relation_symbols[node_value - 3]
                arity = len(symbol.input_sorts)

                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        *(subterm.get_well_formedness_constraint(sort) for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])),
                        *(subterm.get_is_null_constraint() for subterm in self.subterms[arity:]),
                    ),
                    constraint,
                )

        return constraint

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        """
        Interpret the undetermined atomic formula in the given structure and valuation
        """

        interp = smt.FALSE()

        for node_value in range(1, 3 + len(self.language.relation_symbols)):
            if node_value == 1:
                interp = smt.Ite(self.node.equals(node_value), smt.FALSE(), interp)

            elif node_value == 2:
                interp = smt.Ite(self.node.equals(node_value), smt.TRUE(), interp)

            else:
                symbol = self.language.relation_symbols[node_value - 3]
                arity = len(symbol.input_sorts)
                arguments = tuple(
                    subterm.interpret_as_sort(sort, structure, valuation)
                    for sort, subterm in zip(symbol.input_sorts, self.subterms[:arity])
                )
                interp = smt.Ite(self.node.equals(node_value), structure.interpret_relation(symbol, *arguments), interp)

        return interp


class QuantifierFreeFormulaTemplate(Formula):
    """
    To synthesize a quantifier free formula in a given language
    """

    def __init__(self, language: Language, free_vars: Tuple[Variable, ...], term_depth: int, formula_depth: int):
        self.language = language
        self.term_depth = term_depth
        self.formula_depth = formula_depth

        self.node = BoundedIntegerVariable(0, 6) # see get_constructor_and_arity(...)
        self.atom = AtomicFormulaTemplate(language, free_vars, term_depth)

        if formula_depth == 0:
            self.subformulas: Tuple[QuantifierFreeFormulaTemplate, ...] = ()
        else:
            self.subformulas = (
                QuantifierFreeFormulaTemplate(language, free_vars, term_depth, formula_depth - 1),
                QuantifierFreeFormulaTemplate(language, free_vars, term_depth, formula_depth - 1),
            )

    def get_constructor_and_arity(self, node_value: int) -> Tuple[Callable[..., Formula], int]:
        return {
            # 0 for null
            # 1 for root
            2: (Conjunction, 2),
            3: (Disjunction, 2),
            4: (Negation, 1),
            5: (Implication, 2),
            6: (Equivalence, 2),
        }[node_value]

    def get_free_variables(self) -> Set[Variable]:
        free_vars = self.atom.get_free_variables()

        for subformula in self.subformulas:
            free_vars.update(subformula.get_free_variables())

        return free_vars

    def substitute(self, substitution: Mapping[Variable, Term]) -> QuantifierFreeFormulaTemplate:
        new_formula = QuantifierFreeFormulaTemplate(self.language, (), self.term_depth, self.formula_depth)
        new_formula.atom = self.atom.substitute(substitution)
        new_formula.subformulas = tuple(subformula.substitute(substitution) for subformula in self.subformulas)
        return new_formula

    def get_is_null_constraint(self) -> smt.SMTTerm:
        return smt.And(
            self.node.equals(0),
            self.atom.get_is_null_constraint(),
            *(subformula.get_is_null_constraint() for subformula in self.subformulas),
        )

    def get_constraint(self) -> smt.SMTTerm:
        constraint = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value == 1:
                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        self.atom.get_constraint(),
                        *(subformula.get_is_null_constraint() for subformula in self.subformulas),
                    ),
                    constraint,
                )
            
            elif node_value != 0 and self.formula_depth != 0:
                _, arity = self.get_constructor_and_arity(node_value)
                constraint = smt.Or(
                    smt.And(
                        self.node.equals(node_value),
                        self.atom.get_is_null_constraint(),
                        *(subformula.get_constraint() for subformula in self.subformulas[:arity]),
                        *(subformula.get_is_null_constraint() for subformula in self.subformulas[arity:]),
                    ),
                    constraint,
                )

        return constraint

    def get_from_smt_model(self, model: smt.SMTModel) -> Formula:
        node_value = self.node.get_from_smt_model(model)
        assert node_value != 0, "null formula"

        if node_value == 1:
            return self.atom.get_from_smt_model(model)

        elif self.formula_depth != 0:
            constructor, arity = self.get_constructor_and_arity(node_value)
            return constructor(*(subformula.get_from_smt_model(model) for subformula in self.subformulas[:arity]))

        assert False, f"invalid node value {node_value} at depth {self.formula_depth}"
    
    def equals(self, value: Formula) -> smt.SMTTerm:
        if isinstance(value, Falsum) or \
           isinstance(value, Verum) or \
           isinstance(value, RelationApplication):
            return self.atom.equals(value)

        if self.formula_depth == 0:
            return smt.FALSE()

        if isinstance(value, Conjunction):
            return smt.And(
                self.node.equals(2),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )
        
        elif isinstance(value, Disjunction):
            return smt.And(
                self.node.equals(3),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )

        elif isinstance(value, Negation):
            return smt.And(
                self.node.equals(4),
                self.subformulas[0].equals(value.formula),
            )

        elif isinstance(value, Implication):
            return smt.And(
                self.node.equals(5),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )

        elif isinstance(value, Equivalence):
            return smt.And(
                self.node.equals(6),
                self.subformulas[0].equals(value.left),
                self.subformulas[1].equals(value.right),
            )
        
        else:
            return smt.FALSE()

    def interpret(self, structure: Structure, valuation: Mapping[Variable, smt.SMTTerm]) -> smt.SMTTerm:
        interp = smt.FALSE()

        for node_value in self.node.get_range():
            if node_value == 1:
                interp = smt.Ite(
                    self.node.equals(node_value),
                    self.atom.interpret(structure, valuation),
                    interp,
                )

            elif self.formula_depth != 0:
                if node_value == 2:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.And(
                            self.subformulas[0].interpret(structure, valuation),
                            self.subformulas[1].interpret(structure, valuation),
                        ),
                        interp,
                    )

                elif node_value == 3:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Or(
                            self.subformulas[0].interpret(structure, valuation),
                            self.subformulas[1].interpret(structure, valuation),
                        ),
                        interp,
                    )

                elif node_value == 4:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Not(self.subformulas[0].interpret(structure, valuation)),
                        interp,
                    )

                elif node_value == 5:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Implies(
                            self.subformulas[0].interpret(structure, valuation),
                            self.subformulas[1].interpret(structure, valuation),
                        ),
                        interp,
                    )

                elif node_value == 6:
                    interp = smt.Ite(
                        self.node.equals(node_value),
                        smt.Iff(
                            self.subformulas[0].interpret(structure, valuation),
                            self.subformulas[1].interpret(structure, valuation),
                        ),
                        interp,
                    )

        return interp
