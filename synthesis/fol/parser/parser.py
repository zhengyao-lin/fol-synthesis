from typing import Any, List

from lark import Lark, Transformer, Token, Tree

from .ast import *
from .resolver import Resolver


class ASTTransformer(Transformer[BaseAST]):
    def identifier(self, args: List[Token]) -> str:
        return str(args[0])

    def string(self, args: List[Token]) -> str:
        value = str(args[0])
        assert value.startswith("\"") and value.endswith("\"")
        return value[1:-1]

    def natural(self, args: List[Token]) -> int:
        value = str(args[0])
        return int(value)

    def theories(self, args: List[UnresolvedTheory]) -> Tuple[UnresolvedTheory, ...]:
        return tuple(args)

    def theory(self, args: List[Any]) -> UnresolvedTheory:
        name, sentences = args
        return UnresolvedTheory(name, (), Language((), (), ()), sentences)

    def extended_theory(self, args: List[Any]) -> UnresolvedTheory:
        name, base_theories, sentences = args
        return UnresolvedTheory(name, base_theories, Language((), (), ()), sentences)

    def subtheories(self, args: List[Any]) -> Tuple[str, ...]:
        return tuple(args)

    def attribute_argument(self, args: List[Union[str, int]]) -> Union[str, int]:
        return args[0]

    def attribute(self, args: List[Union[str, int]]) -> Attribute:
        name, *arguments = args
        assert isinstance(name, str)
        return Attribute(name, tuple(arguments))

    def attributes(self, args: List[Attribute]) -> Tuple[Attribute, ...]:
        return tuple(args)

    def sentences(self, args: List[Sentence]) -> Tuple[Sentence, ...]:
        return tuple(args)

    def sort_definition(self, args: List[Any]) -> UnresolvedSortDefinition:
        sort_name, attributes = args
        return UnresolvedSortDefinition(Sort(sort_name), attributes)

    def function_definition(self, args: List[Any]) -> UnresolvedFunctionDefinition:
        name, *input_sorts, output_sort, attributes = args
        return UnresolvedFunctionDefinition(name, tuple(input_sorts), output_sort, attributes)

    def constant_definition(self, args: List[Any]) -> UnresolvedFunctionDefinition:
        name, output_sort, attributes = args
        return UnresolvedFunctionDefinition(name, (), output_sort, attributes)

    def relation_definition(self, args: List[Any]) -> UnresolvedRelationDefinition:
        name, *input_sorts, attributes = args
        return UnresolvedRelationDefinition(name, tuple(input_sorts), attributes)

    def fixpoint_definition(self, args: List[Any]) -> UnresolvedFixpointDefinition:
        name, *variables, formula, attributes = args
        return UnresolvedFixpointDefinition(name, tuple(variables), formula, attributes)

    def axiom(self, args: List[Formula]) -> Axiom:
        formula, = args
        return Axiom(formula)

    def terms(self, args: List[Term]) -> Tuple[Term, ...]:
        return tuple(args)

    def variable(self, args: List[str]) -> UnresolvedVariable:
        if len(args) == 1:
            return UnresolvedVariable(args[0])
        else:
            return UnresolvedVariable(args[0], args[1])

    def function_application(self, args: List[Any]) -> UnresolvedApplication:
        name, arguments = args
        return UnresolvedApplication(name, tuple(arguments))

    def verum(self, args: List[Tree]) -> Verum:
        return Verum()

    def falsum(self, args: List[Tree]) -> Falsum:
        return Falsum()

    def paren_formula(self, args: List[Formula]) -> Formula:
        return args[0]

    def relation_application(self, args: List[Any]) -> UnresolvedRelationApplication:
        name, arguments = args
        return UnresolvedRelationApplication(name, tuple(arguments))

    def equality(self, args: List[Term]) -> Equality:
        left, right = args
        return Equality(left, right)

    def disequality(self, args: List[Term]) -> Formula:
        left, right = args
        return Negation(Equality(left, right))

    def negation(self, args: List[Formula]) -> Negation:
        _, formula = args
        return Negation(formula)

    def conjunction(self, args: List[Formula]) -> Formula:
        assert len(args) != 0
        formula = args[0]
        for conjunct in args[1:]:
            formula = Conjunction(formula, conjunct)
        return formula

    def disjunction(self, args: List[Formula]) -> Formula:
        assert len(args) != 0
        formula = args[0]
        for disjunct in args[1:]:
            formula = Disjunction(formula, disjunct)
        return formula

    def implication(self, args: List[Formula]) -> Formula:
        assert len(args) != 0
        formula = args[-1]
        for implicant in args[:-1][::-1]:
            formula = Implication(implicant, formula)
        return formula

    def equivalence(self, args: List[Formula]) -> Formula:
        if len(args) == 1: return args[0]
        left, right = args
        return Equivalence(left, right)

    def universal_quantification(self, args: List[Formula]) -> Formula:
        _, *variables, formula = args
        for variable in variables[::-1]:
            assert isinstance(variable, UnresolvedVariable)
            formula = UnresolvedUniversalQuantification(variable, formula)
        return formula

    def existential_quantification(self, args: List[Formula]) -> Formula:
        _, *variables, formula = args
        for variable in variables[::-1]:
            assert isinstance(variable, UnresolvedVariable)
            formula = UnresolvedExistentialQuantification(variable, formula)
        return formula


class Parser:
    SYNTAX = r"""
        %import common.ESCAPED_STRING -> STRING

        INLINE_COMMENT: /\/\/[^\n]*/
        BLOCK_COMMENT: /\/\*((.|\n)(?<!\*\/))*\*\//

        %ignore INLINE_COMMENT
        %ignore BLOCK_COMMENT
        %ignore /[ \n\t\f\r]+/

        IDENTIFIER: /[A-Za-z][A-Za-z0-9-_']*/
        TRUE.2: "true"
        FALSE.2: "false"

        NEGATION.2: "not" | "¬"

        FORALL.2: "forall"
        EXISTS.2: "exists"

        NATURAL: /0|[1-9][0-9]*/

        identifier: IDENTIFIER
        string: STRING
        natural: NATURAL

        theories: theory+

        theory: "theory" identifier sentences "end"
              | "theory" identifier "extending" subtheories sentences "end" -> extended_theory

        attribute_argument: string | natural

        attribute: identifier "(" attribute_argument ["," attribute_argument]* ")"
                 | identifier

        attributes: ["[" attribute ["," attribute]* "]"]

        sentences: [sentence sentence*]
        subtheories: identifier+

        sentence: "sort" identifier attributes                                                    -> sort_definition
                | "function" identifier ":" identifier+ "->" identifier attributes                -> function_definition
                | "constant" identifier ":" identifier attributes                                 -> constant_definition
                | "relation" identifier ":" identifier* attributes                                -> relation_definition
                | "fixpoint" identifier "(" [variable ("," variable)*] ")" "=" formula attributes -> fixpoint_definition
                | "axiom" formula                                                                 -> axiom

        terms: [term ("," term)*]

        variable: identifier [":" identifier]
        quantified_variable: identifier ":" identifier -> variable

        ?term: variable
             | identifier "(" terms ")" -> function_application

        // '?' here means that if the production only has one non-terminal e.g. negation -> atomic
        // the transformer of 'atomic' will be called instead of 'negation'

        atomic: TRUE                     -> verum
              | FALSE                    -> falsum
              | term "=" term            -> equality
              | term "!=" term           -> disequality
              | "(" formula ")"          -> paren_formula
              | identifier "(" terms ")" -> relation_application

        ?negation: atomic | NEGATION atomic
        ?negation_quant: quantification | NEGATION quantification -> negation

        ?conjunction: negation ("/\\" negation)*
        ?conjunction_quant: [negation ("/\\" negation)* "/\\"] negation_quant -> conjunction

        ?disjunction: conjunction ("\\/" conjunction)*
        ?disjunction_quant: [conjunction ("\\/" conjunction)* "\\/"] conjunction_quant -> disjunction

        ?implication: disjunction ("->" disjunction)*
        ?implication_quant: [disjunction ("->" disjunction)* "->"] disjunction_quant -> implication

        ?equivalence: [implication "<->"] implication
                    | [implication "<->"] implication_quant -> equivalence

        ?formula: equivalence

        quantification: FORALL quantified_variable ["," quantified_variable]+ "." formula -> universal_quantification
                      | EXISTS quantified_variable ["," quantified_variable]+ "." formula -> existential_quantification
    """

    THEORY_PARSER = Lark(
        SYNTAX,
        start="theory",
        parser="lalr",
        lexer="standard",
        propagate_positions=True,
    )

    THEORIES_PARSER = Lark(
        SYNTAX,
        start="theories",
        parser="lalr",
        lexer="standard",
        propagate_positions=True,
    )

    TERM_PARSER = Lark(
        SYNTAX,
        start="term",
        parser="lalr",
        lexer="standard",
        propagate_positions=True,
    )

    FORMULA_PARSER = Lark(
        SYNTAX,
        start="formula",
        parser="lalr",
        lexer="standard",
        propagate_positions=True,
    )

    @staticmethod
    def parse_theory(src: str) -> Theory:
        ast = Parser.THEORY_PARSER.parse(src)
        theory = ASTTransformer().transform(ast)
        assert isinstance(theory, UnresolvedTheory)
        return Resolver.resolve_theory(theory)

    @staticmethod
    def parse_theories(src: str) -> Dict[str, Theory]:
        ast = Parser.THEORIES_PARSER.parse(src)
        theories = ASTTransformer().transform(ast)
        assert isinstance(theories, tuple)
        return Resolver.resolve_theories(theories)

    @staticmethod
    def parse_term(language: Language, src: str) -> Term:
        ast = Parser.TERM_PARSER.parse(src)
        term = ASTTransformer().transform(ast)
        assert isinstance(term, Term)
        return Resolver.resolve_term(language, term)

    @staticmethod
    def parse_formula(language: Language, src: str) -> Formula:
        ast = Parser.FORMULA_PARSER.parse(src)
        formula = ASTTransformer().transform(ast)
        assert isinstance(formula, Formula)
        return Resolver.resolve_formula(language, formula)
