from typing import TypeVar, Any, overload, Dict, Type
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
    def visit(self, ast: FixpointDefinition) -> FixpointDefinition: ...

    @overload
    def visit(self, ast: Axiom) -> Axiom: ...

    @overload
    def visit(self, ast: Sentence) -> Sentence: ...

    @overload
    def visit(self, ast: UnresolvedTheory) -> UnresolvedTheory: ...

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

    def visit_equality(self, equality: Equality) -> Equality:
        return Equality(
            self.visit(equality.left),
            self.visit(equality.right),
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
            definition.bound,
        )

    def visit_axiom(self, axiom: Axiom) -> Axiom:
        return Axiom(self.visit(axiom.formula))

    def visit_theory(self, theory: Theory) -> Theory:
        return Theory(
            theory.language,
            { symbol: self.visit(definition) for symbol, definition in theory.fixpoint_definitions.items() },
            tuple(self.visit(axiom) for axiom in theory.axioms),
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
            definition.attributes,
        )

    def visit_unresolved_theory(self, theory: UnresolvedTheory) -> Union[Theory, UnresolvedTheory]:
        return UnresolvedTheory(
            theory.name,
            theory.base_theory_names,
            theory.language,
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
        return Variable(variable.name, sort)

    def visit_unresolved_application(self, application: UnresolvedApplication) -> Application:
        symbol = self.language.get_function_symbol(application.name)
        assert len(application.arguments) == len(symbol.input_sorts), \
               f"function symbol {application.name} has {len(symbol.input_sorts)} arguments, but {len(application.arguments)} are given"
        return Application(
            symbol,
            tuple(self.visit(argument) for argument in application.arguments),
        )

    def visit_unresolved_relation_application(self, application: UnresolvedRelationApplication) -> RelationApplication:
        symbol = self.language.get_relation_symbol(application.name)
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
        assert len(definition.variables) == len(symbol.input_sorts), \
               f"relation symbol {definition.name} has {len(symbol.input_sorts)} arguments, but {len(definition.variables)} are given"

        variables = []

        for i, (variable, sort) in enumerate(zip(definition.variables, symbol.input_sorts)):
            if variable.sort is not None:
                assert variable.sort == sort.name, \
                       f"the {i}-th argument of {definition.name} has sort {sort}, but the argument has sort annotation {variable.sort}"
            variables.append(Variable(variable.name, sort))

        bound: Optional[int] = None

        for attribute in definition.attributes:
            if attribute.name == "bound":
                assert bound is None, f"duplicate attribute {attribute}"
                assert len(attribute.arguments) == 1 and isinstance(attribute.arguments[0], int), \
                       f"invalid attribute format {attribute}"
                bound = attribute.arguments[0]
            else:
                assert False, f"unknown attribute {attribute}"

        return FixpointDefinition(symbol, tuple(variables), self.visit(definition.definition), bound)


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
            definition.bound,
        )
        self.sorting_environment = {}

        return resolved


class Resolver:
    @staticmethod
    def get_attribute(attributes: Tuple[Attribute, ...], name: str, arg_types: Tuple[Any, ...]) -> Optional[Tuple[Union[int, str], ...]]:
        args: Optional[Tuple[Union[int, str], ...]] = None

        for attribute in attributes:
            if attribute.name == name:
                assert args is None, f"duplicate attribute {name}"
                args = attribute.arguments

        if args is None:
            return None

        if len(args) != len(arg_types):
            return None

        for arg, arg_type in zip(args, arg_types):
            if not isinstance(arg, arg_type):
                return None

        return args

    @staticmethod
    def collect_sorts(theory: UnresolvedTheory) -> Tuple[Sort, ...]:
        sorts = []

        for sentence in theory.sentences:
            if isinstance(sentence, UnresolvedSortDefinition):
                sort = sentence.sort
                
                smt_args = Resolver.get_attribute(sentence.attributes, "smt", (str,))
                if smt_args is not None:
                    assert isinstance(smt_args[0], str)
                    sort = Sort(sort.name, smt_hook=smt.SMTLIB.parse_sort(smt_args[0]))
                else:
                    # a refinement sort
                    smt_args = Resolver.get_attribute(sentence.attributes, "smt", (str, str))
                    if smt_args is not None:
                        assert isinstance(smt_args[0], str) and isinstance(smt_args[1], str)
                        sort = Sort(
                            sort.name,
                            smt_hook=smt.SMTLIB.parse_sort(smt_args[0]),
                            smt_hook_constraint=smt.SMTLIB.parse_smt_function_from_template(smt_args[1]),
                        )

                assert sort not in sorts, f"duplicate sort {sort} in theory {theory.name}"

                sorts.append(sort)

        return tuple(sorts)

    @staticmethod
    def resolve_language(theory: UnresolvedTheory) -> UnresolvedTheory:
        """
        Collect sort, function, and relation symbols from a theory
        """

        assert len(theory.base_theory_names) == 0, \
               f"expecting no theory import, got {theory.base_theory_names}"

        sorts = Resolver.collect_sorts(theory)
        sort_map = { sort.name: sort for sort in sorts }

        function_symbols = OrderedDict()
        relation_symbols = OrderedDict()
        other_sentences = []

        for sentence in theory.sentences:
            if isinstance(sentence, UnresolvedFunctionDefinition):
                assert sentence.output_sort in sort_map, \
                       f"unknown sort {sentence.output_sort} in theory {theory.name}"
                output_sort = sort_map[sentence.output_sort]

                input_sorts = []
                for name in sentence.input_sorts:
                    assert name in sort_map, f"unknown sort {name} in theory {theory.name}"
                    input_sorts.append(sort_map[name])

                smt_args = Resolver.get_attribute(sentence.attributes, "smt", (str,))
                if smt_args is not None:
                    assert isinstance(smt_args[0], str)
                    smt_hook: Optional[smt.SMTFunction] = smt.SMTLIB.parse_smt_function_from_template(smt_args[0])
                else:
                    smt_hook = None

                assert sentence.name not in function_symbols, \
                       f"duplicated function symbol {sentence.name} in theory {theory.name}"
                function_symbols[sentence.name] = FunctionSymbol(tuple(input_sorts), output_sort, sentence.name, smt_hook)

            elif isinstance(sentence, UnresolvedRelationDefinition):
                input_sorts = []
                for name in sentence.input_sorts:
                    assert name in sort_map, f"unknown sort {name} in theory {theory.name}"
                    input_sorts.append(sort_map[name])

                smt_args = Resolver.get_attribute(sentence.attributes, "smt", (str,))
                if smt_args is not None:
                    assert isinstance(smt_args[0], str)
                    smt_hook = smt.SMTLIB.parse_smt_function_from_template(smt_args[0])
                else:
                    smt_hook = None

                assert sentence.name not in relation_symbols, \
                       f"duplicated relation symbol {sentence.name} in theory {theory.name}"
                relation_symbols[sentence.name] = RelationSymbol(tuple(input_sorts), sentence.name, smt_hook)

            elif not isinstance(sentence, UnresolvedSortDefinition):
                other_sentences.append(sentence)

        language = Language(sorts, tuple(function_symbols.values()), tuple(relation_symbols.values()))

        return UnresolvedTheory(theory.name, theory.base_theory_names, language, tuple(other_sentences))

    @staticmethod
    def resolve_theory(theory: UnresolvedTheory) -> Theory:
        resolved = Resolver.resolve_language(theory)
        resolved = SymbolResolver(resolved.language).visit(resolved)
        resolved = VariableSortResolver(resolved.language).visit(resolved)

        fixpoint_definitions: Dict[RelationSymbol, FixpointDefinition] = {}
        axioms: List[Axiom] = []

        for sentence in resolved.sentences:
            if isinstance(sentence, Axiom):
                axioms.append(sentence)
            elif isinstance(sentence, FixpointDefinition):
                assert sentence.relation_symbol not in fixpoint_definitions, \
                       f"duplicate fixpoint definitions for {sentence.relation_symbol}"
                fixpoint_definitions[sentence.relation_symbol] = sentence

        # TODO: do a final sort check
        
        return Theory(resolved.language, fixpoint_definitions, tuple(axioms))

    @staticmethod
    def resolve_theories(theories: Tuple[UnresolvedTheory, ...]) -> Dict[str, Theory]:
        """
        Resolve a list of theories that may extend each other
        """
        theory_map: Dict[str, UnresolvedTheory] = {}
        theory_imports: Dict[str, Set[str]] = {}

        for theory in theories:
            theory_map[theory.name] = theory
            theory_imports[theory.name] = set(theory.base_theory_names)

        # compute the set of theories each theory extends from
        changed = True
        while changed:
            changed = False

            for theory in theory_map.values():
                assert theory.name not in theory_imports[theory.name], \
                       f"circular imports from theory {theory.name}"

                for base_theory_name in theory.base_theory_names:
                    assert base_theory_name in theory_imports, \
                           f"theory {base_theory_name} not found"

                    if not theory_imports[theory.name].issuperset(theory_imports[base_theory_name]):
                        theory_imports[theory.name].update(theory_imports[base_theory_name])
                        changed = True

        extended_theories: List[UnresolvedTheory] = []

        # actually extend the theories
        for theory in theory_map.values():
            new_sentences = theory.sentences

            for base_theory_name in sorted(theory_imports[theory.name]):
                new_sentences += theory_map[base_theory_name].sentences

            # create a new theory
            extended_theories.append(UnresolvedTheory(
                theory.name,
                (),
                theory.language,
                new_sentences,
            ))

        # then resolve each theory
        return { theory.name: Resolver.resolve_theory(theory) for theory in extended_theories }

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