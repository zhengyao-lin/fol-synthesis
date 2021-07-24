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

    def theory(self, args: List[Any]) -> UnresolvedTheory:
        name, sentences = args
        return UnresolvedTheory(name, tuple(sentences))

    def attribute(self, args: List[str]) -> Attribute:
        name, *arguments = args
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
        name, *variables, formula = args
        return UnresolvedFixpointDefinition(name, tuple(variables), formula)

    def axiom(self, args: List[Formula]) -> Axiom:
        formula, = args
        return Axiom(formula)

    def fol_terms(self, args: List[Term]) -> Tuple[Term, ...]:
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

    def fol_negation(self, args: List[Formula]) -> Negation:
        _, formula = args
        return Negation(formula)

    def fol_conjunction(self, args: List[Formula]) -> Formula:
        assert len(args) != 0
        formula = args[0]
        for conjunct in args[1:]:
            formula = Conjunction(formula, conjunct)
        return formula

    def fol_disjunction(self, args: List[Formula]) -> Formula:
        assert len(args) != 0
        formula = args[0]
        for disjunct in args[1:]:
            formula = Disjunction(formula, disjunct)
        return formula

    def fol_implication(self, args: List[Formula]) -> Formula:
        assert len(args) != 0
        formula = args[-1]
        for implicant in args[:-1][::-1]:
            formula = Implication(implicant, formula)
        return formula

    def fol_equivalence(self, args: List[Formula]) -> Formula:
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

        NEGATION.2: "not"

        FORALL.2: "forall"
        EXISTS.2: "exists"

        identifier: IDENTIFIER
        string: STRING

        theory: "theory" identifier sentences "end"

        attribute: identifier "(" string ["," string]* ")"
                 | identifier

        attributes: ["[" attribute ["," attribute]* "]"]

        sentences: [sentence sentence*]
        subtheories: [identifier identifier*]

        sentence: "sort" identifier attributes                                             -> sort_definition
                | "function" identifier ":" identifier+ "->" identifier attributes         -> function_definition
                | "constant" identifier ":" identifier attributes                          -> constant_definition
                | "relation" identifier ":" identifier* attributes                         -> relation_definition
                | "fixpoint" identifier "(" [variable ("," variable)*] ")" "=" fol_formula -> fixpoint_definition
                | "axiom" fol_formula                                                      -> axiom

        fol_terms: [fol_term ("," fol_term)*]

        variable: identifier [":" identifier]
        quantified_variable: identifier ":" identifier -> variable

        ?fol_term: variable
                 | identifier "(" fol_terms ")" -> function_application

        // '?' here means that if the production only has one non-terminal e.g. fol_negation -> fol_atomic
        // the transformer of 'fol_atomic' will be called instead of 'fol_negation'

        fol_atomic: TRUE                         -> verum
                  | FALSE                        -> falsum
                  // | fol_term "=" fol_term     -> equality
                  | "(" fol_formula ")"          -> paren_formula
                  | identifier "(" fol_terms ")" -> relation_application

        ?fol_negation: fol_atomic | NEGATION fol_atomic
        ?fol_negation_quant: fol_quantification | NEGATION fol_quantification -> fol_negation

        ?fol_conjunction: fol_negation ("/\\" fol_negation)*
        ?fol_conjunction_quant: [fol_negation ("/\\" fol_negation)* "/\\"] fol_negation_quant -> fol_conjunction

        ?fol_disjunction: fol_conjunction ("\\/" fol_conjunction)*
        ?fol_disjunction_quant: [fol_conjunction ("\\/" fol_conjunction)* "\\/"] fol_conjunction_quant -> fol_disjunction

        ?fol_implication: fol_disjunction ("->" fol_disjunction)*
        ?fol_implication_quant: [fol_disjunction ("->" fol_disjunction)* "->"] fol_disjunction_quant -> fol_implication

        ?fol_equivalence: [fol_implication "<->"] fol_implication
                        | [fol_implication "<->"] fol_implication_quant -> fol_equivalence

        ?fol_formula: fol_equivalence

        fol_quantification: FORALL quantified_variable ["," quantified_variable]+ "." fol_formula -> universal_quantification
                          | EXISTS quantified_variable ["," quantified_variable]+ "." fol_formula -> existential_quantification
    """

    THEORY_PARSER = Lark(
        SYNTAX,
        start="theory",
        parser="lalr",
        lexer="standard",
        propagate_positions=True,
    )

    @staticmethod
    def parse_theory(src: str) -> Theory:
        ast = Parser.THEORY_PARSER.parse(src)
        theory = ASTTransformer().transform(ast)
        assert isinstance(theory, UnresolvedTheory)
        return Resolver.resolve(theory)
