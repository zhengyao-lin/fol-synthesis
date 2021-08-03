from typing import TypeVar, Any, overload, Dict
from collections import OrderedDict

import re

from .ast import *


AST = TypeVar("AST", bound=BaseAST)


class CopyVisitor:
    CAMEL_TO_SNAKE = re.compile(r"(?<!^)(?=[A-Z])")

    @overload
    def visit(self, ast: Variable) -> Variable: ...

    @overload
    def visit(self, ast: UnresolvedVariable) -> Union[Variable, UnresolvedVariable]: ...

    @overload
    def visit(self, ast: Application) -> Application: ...

    @overload
    def visit(self, ast: UnresolvedApplication) -> Union[Application, UnresolvedApplication]: ...

    @overload
    def visit(self, ast: Term) -> Term: ...

    @overload
    def visit(self, ast: Formula) -> Formula: ...

    @overload
    def visit(self, ast: Sentence) -> Sentence: ...

    @overload
    def visit(self, ast: UnresolvedTheory) -> Union[Theory, UnresolvedTheory]: ...

    @overload
    def visit(self, ast: Theory) -> Theory: ...

    def visit(self, ast: Any) -> Any:
        # automatically change the camel case name of the ast class
        # to snake case and call the corresponding visitor
        class_name = type(ast).__name__
        visitor_name = "visit_" + CopyVisitor.CAMEL_TO_SNAKE.sub("_", class_name).lower()
        return getattr(self, visitor_name)(ast)

    def visit_variable(self, variable: Variable) -> Variable:
        return variable

    def visit_application(self, application: Application) -> Application:
        return Application(
            application.function_symbol,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_verum(self, verum: Verum) -> Verum:
        return verum

    def visit_falsum(self, falsum: Falsum) -> Falsum:
        return falsum

    def visit_relation_application(self, application: RelationApplication) -> RelationApplication:
        return RelationApplication(
            application.relation_symbol,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_conjunction(self, conjunction: Conjunction) -> Conjunction:
        return Conjunction(
            self.visit(conjunction.left),
            self.visit(conjunction.right),
        )

    def visit_disjunction(self, disjunction: Disjunction) -> Disjunction:
        return Disjunction(
            self.visit(disjunction.left),
            self.visit(disjunction.right),
        )

    def visit_negation(self, negation: Negation) -> Negation:
        return Negation(self.visit(negation.formula))

    def visit_implication(self, implication: Implication) -> Implication:
        return Implication(
            self.visit(implication.left),
            self.visit(implication.right),
        )

    def visit_equivalence(self, equivalence: Equivalence) -> Equivalence:
        return Equivalence(
            self.visit(equivalence.left),
            self.visit(equivalence.right),
        )

    def visit_universal_quantification(self, formula: UniversalQuantification) -> UniversalQuantification:
        return UniversalQuantification(
            self.visit(formula.variable),
            self.visit(formula.body),
        )
    
    def visit_existential_quantification(self, formula: ExistentialQuantification) -> ExistentialQuantification:
        return ExistentialQuantification(
            self.visit(formula.variable),
            self.visit(formula.body),
        )

    def visit_fixpoint_definition(self, definition: FixpointDefinition) -> FixpointDefinition:
        return FixpointDefinition(
            definition.relation_symbol,
            tuple(self.visit(variable) for variable in definition.variables),
            self.visit(definition.definition),
        )

    def visit_axiom(self, axiom: Axiom) -> Axiom:
        return Axiom(self.visit(axiom.formula))

    def visit_theory(self, theory: Theory) -> Theory:
        return Theory(
            theory.language,
            tuple(self.visit(sentence) for sentence in theory.sentences),
        )

    def visit_unresolved_variable(self, variable: UnresolvedVariable) -> Union[Variable, UnresolvedVariable]:
        return variable

    def visit_unresolved_application(self, application: UnresolvedApplication) -> Term:
        return UnresolvedApplication(
            application.name,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_unresolved_relation_application(self, application: UnresolvedRelationApplication) -> Formula:
        return UnresolvedRelationApplication(
            application.name,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_unresolved_universal_quantification(self, formula: UnresolvedUniversalQuantification) -> Formula:
        return UnresolvedUniversalQuantification(
            formula.variable,
            self.visit(formula.body),
        )

    def visit_unresolved_existential_quantification(self, formula: UnresolvedExistentialQuantification) -> Formula:
        return UnresolvedExistentialQuantification(
            formula.variable,
            self.visit(formula.body),
        )

    def visit_unresolved_sort_definition(self, definition: UnresolvedSortDefinition) -> Sentence:
        return definition

    def visit_unresolved_function_definition(self, definition: UnresolvedFunctionDefinition) -> Sentence:
        return definition

    def visit_unresolved_relation_definition(self, definition: UnresolvedRelationDefinition) -> Sentence:
        return definition

    def visit_unresolved_fixpoint_definition(self, definition: UnresolvedFixpointDefinition) -> Sentence:
        return UnresolvedFixpointDefinition(
            definition.name,
            definition.variables,
            self.visit(definition.definition),
        )

    def visit_unresolved_theory(self, theory: UnresolvedTheory) -> Union[Theory, UnresolvedTheory]:
        return UnresolvedTheory(
            theory.name,
            tuple(self.visit(sentence) for sentence in theory.sentences),
        )


class SymbolResolver(CopyVisitor):
    """
    Resolve all references to sorts, function symbols, and relation symbols
    """

    def __init__(self, language: Language):
        super().__init__()
        self.language = language

    def visit_unresolved_variable(self, variable: UnresolvedVariable) -> Union[Variable, UnresolvedVariable]:
        if variable.sort is None:
            return variable
        sort = self.language.get_sort(variable.sort)
        assert sort is not None, \
               f"sort {sort} is not defined"
        return Variable(variable.name, sort)

    def visit_unresolved_application(self, application: UnresolvedApplication) -> Application:
        symbol = self.language.get_function_symbol(application.name)
        assert symbol is not None, \
               f"function symbol {application.name} is not defined"
        assert len(application.arguments) == len(symbol.input_sorts), \
               f"function symbol {application.name} has {len(symbol.input_sorts)} arguments, but {len(application.arguments)} are given"
        return Application(
            symbol,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_unresolved_relation_application(self, application: UnresolvedRelationApplication) -> RelationApplication:
        symbol = self.language.get_relation_symbol(application.name)
        assert symbol is not None, \
               f"relation symbol {application.name} is not defined"
        assert len(application.arguments) == len(symbol.input_sorts), \
               f"relation symbol {application.name} has {len(symbol.input_sorts)} arguments, but {len(application.arguments)} are given"
        return RelationApplication(
            symbol,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_unresolved_universal_quantification(self, formula: UnresolvedUniversalQuantification) -> UniversalQuantification:
        variable = self.visit(formula.variable)
        assert isinstance(variable, Variable), \
               f"sort of the variable has to be declared at the binder"
        return UniversalQuantification(variable, self.visit(formula.body))

    def visit_unresolved_existential_quantification(self, formula: UnresolvedExistentialQuantification) -> ExistentialQuantification:
        variable = self.visit(formula.variable)
        assert isinstance(variable, Variable), \
               f"sort of the variable has to be declared at the binder"
        return ExistentialQuantification(variable, self.visit(formula.body))

    def visit_unresolved_fixpoint_definition(self, definition: UnresolvedFixpointDefinition) -> FixpointDefinition:
        symbol = self.language.get_relation_symbol(definition.name)
        assert symbol is not None, \
               f"relation symbol {definition.name} is not defined"
        
        assert len(definition.variables) == len(symbol.input_sorts), \
               f"relation symbol {definition.name} has {len(symbol.input_sorts)} arguments, but {len(definition.variables)} are given"

        variables = []

        for i, (variable, sort) in enumerate(zip(definition.variables, symbol.input_sorts)):
            if variable.sort is not None:
                assert variable.sort == sort.name, \
                       f"the {i}-th argument of {definition.name} has sort {sort}, but the argument has sort annotation {variable.sort}"
            variables.append(Variable(variable.name, sort))

        return FixpointDefinition(symbol, tuple(variables), self.visit(definition.definition))


class VariableSortResolver(CopyVisitor):
    """
    Annotate all variables without sort annotation
    """

    def __init__(self, language: Language):
        super().__init__()
        self.language = language
        self.sorting_environment: Dict[str, Sort] = {}

    def visit_unresolved_variable(self, variable: UnresolvedVariable) -> Variable:
        assert variable.name in self.sorting_environment, \
               f"free variable {variable} is not allowed in sentences"
        return Variable(variable.name, self.sorting_environment[variable.name])

    def visit_universal_quantification(self, formula: UniversalQuantification) -> UniversalQuantification:
        old_sort = self.sorting_environment.get(formula.variable.name)
        self.sorting_environment[formula.variable.name] = formula.variable.sort

        resolved = UniversalQuantification(formula.variable, self.visit(formula.body))

        if old_sort is not None:
            self.sorting_environment[formula.variable.name] = old_sort
        else:
            del self.sorting_environment[formula.variable.name]

        return resolved

    def visit_existential_quantification(self, formula: ExistentialQuantification) -> ExistentialQuantification:
        old_sort = self.sorting_environment.get(formula.variable.name)
        self.sorting_environment[formula.variable.name] = formula.variable.sort

        resolved = ExistentialQuantification(formula.variable, self.visit(formula.body))

        if old_sort is not None:
            self.sorting_environment[formula.variable.name] = old_sort
        else:
            del self.sorting_environment[formula.variable.name]

        return resolved

    def visit_fixpoint_definition(self, definition: FixpointDefinition) -> FixpointDefinition:
        assert len(self.sorting_environment) == 0

        self.sorting_environment = {
            variable.name: sort
            for variable, sort in zip(definition.variables, definition.relation_symbol.input_sorts)
        }
        resolved = FixpointDefinition(
            definition.relation_symbol,
            definition.variables,
            self.visit(definition.definition),
        )
        self.sorting_environment = {}

        return resolved


class Resolver:
    @staticmethod
    def get_smt_attribute(attributes: Tuple[Attribute, ...]) -> Optional[str]:
        """
        Try to find an SMT attribut in a list of attributes
        """
        for attribute in attributes:
            if attribute.name == "smt":
                assert len(attribute.arguments) == 1, "smt attribute requires exactly one argument"
                return attribute.arguments[0]
        return None

    @staticmethod
    def collect_sorts(theory: UnresolvedTheory) -> Tuple[Sort, ...]:
        sorts = []

        for sentence in theory.sentences:
            if isinstance(sentence, UnresolvedSortDefinition):
                sort = sentence.sort
                
                smt_attribute = Resolver.get_smt_attribute(sentence.attributes)
                if smt_attribute is not None:
                    sort = Sort(sort.name, smt_hook=smt.SMTLIB.parse_sort(smt_attribute))

                sorts.append(sort)

        return tuple(sorts)

    @staticmethod
    def resolve_language(theory: UnresolvedTheory) -> Theory:
        """
        Collect sort, function, and relation symbols from a theory
        """

        sorts = Resolver.collect_sorts(theory)
        sort_map = { sort.name: sort for sort in sorts }

        function_symbols = OrderedDict()
        relation_symbols = OrderedDict()
        other_sentences = []

        for sentence in theory.sentences:
            if isinstance(sentence, UnresolvedFunctionDefinition):
                assert sentence.output_sort in sort_map, \
                       f"unknown sort {sentence.output_sort}"
                output_sort = sort_map[sentence.output_sort]

                input_sorts = []
                for name in sentence.input_sorts:
                    assert name in sort_map, f"unknown sort {name}"
                    input_sorts.append(sort_map[name])

                smt_attribute = Resolver.get_smt_attribute(sentence.attributes)
                if smt_attribute is not None:
                    smt_hook: Optional[smt.SMTFunction] = smt.SMTLIB.parse_smt_function_from_template(smt_attribute)
                else:
                    smt_hook = None

                assert sentence.name not in function_symbols, \
                       f"duplicated function symbol {sentence.name}"
                function_symbols[sentence.name] = FunctionSymbol(tuple(input_sorts), output_sort, sentence.name, smt_hook)

            elif isinstance(sentence, UnresolvedRelationDefinition):
                input_sorts = []
                for name in sentence.input_sorts:
                    assert name in sort_map, f"unknown sort {name}"
                    input_sorts.append(sort_map[name])

                smt_attribute = Resolver.get_smt_attribute(sentence.attributes)
                if smt_attribute is not None:
                    smt_hook = smt.SMTLIB.parse_smt_function_from_template(smt_attribute)
                else:
                    smt_hook = None

                assert sentence.name not in relation_symbols, \
                       f"duplicated relation symbol {sentence.name}"
                relation_symbols[sentence.name] = RelationSymbol(tuple(input_sorts), sentence.name, smt_hook)

            elif not isinstance(sentence, UnresolvedSortDefinition):
                other_sentences.append(sentence)

        language = Language(sorts, tuple(function_symbols.values()), tuple(relation_symbols.values()))

        return Theory(language, tuple(other_sentences))

    @staticmethod
    def resolve_theory(theory: UnresolvedTheory) -> Theory:
        resolved = Resolver.resolve_language(theory)
        resolved = SymbolResolver(resolved.language).visit(resolved)
        resolved = VariableSortResolver(resolved.language).visit(resolved)
        # TODO: do a final sort check
        return resolved

    @staticmethod
    def resolve_term(language: Language, term: Term) -> Term:
        resolved = SymbolResolver(language).visit(term)
        resolved = VariableSortResolver(language).visit(resolved)
        return resolved

    @staticmethod
    def resolve_formula(language: Language, formula: Formula) -> Formula:
        resolved = SymbolResolver(language).visit(formula)
        resolved = VariableSortResolver(language).visit(resolved)
        return resolved