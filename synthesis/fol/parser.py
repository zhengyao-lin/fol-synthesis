from typing import Any

from lark import Lark, Transformer

from .ast import *


class Command:
    pass


class ASTTransformer(Transformer[BaseAST]):
    pass


syntax = r"""
INLINE_COMMENT: /\/\/[^\n]*/
BLOCK_COMMENT: /\/\*((.|\n)(?<!\*\/))*\*\//

%ignore INLINE_COMMENT
%ignore BLOCK_COMMENT
%ignore /[ \n\t\f\r]+/

IDENTIFIER: /[A-Za-z][A-Za-z0-9-_']*/
TRUE.2: "true"
FALSE.2: "false"

NEGATION.2: "not"
CONJUNCTION.2: "/\\"
DISJUNCTION.2: "\\/"
IMPLICATION.2: "->"
EQUIVALENCE.2: "<->"

FORALL.2: "forall"
EXISTS.2: "exists"

theory: "theory" IDENTIFIER ["extending" subtheories] [sentence sentence*] "end"

subtheories: IDENTIFIER IDENTIFIER*

sentence: "sort" IDENTIFIER
        | "function" IDENTIFIER ":" IDENTIFIER+ "->" IDENTIFIER
        | "constant" IDENTIFIER ":" IDENTIFIER
        | "relation" IDENTIFIER ":" IDENTIFIER*
        | "fixpoint" IDENTIFIER "(" [variable ("," variable)*] ")" "=" fol_formula
        | "assert" fol_formula

fol_terms: [fol_term ("," fol_term)*]

variable: IDENTIFIER [":" IDENTIFIER]

fol_term: IDENTIFIER "(" fol_terms ")" -> function_application
        | variable

fol_atomic: TRUE                         -> verum
          | FALSE                        -> falsum
          | fol_term "=" fol_term        -> equality
          | "(" fol_atomic ")"           -> paren_formula
          | IDENTIFIER "(" fol_terms ")" -> relation_application

?fol_negation: fol_atomic | NEGATION fol_atomic
?fol_negation_quant: fol_quantification | NEGATION fol_quantification -> fol_negation

?fol_conjunction: fol_negation (CONJUNCTION fol_negation)*
?fol_conjunction_quant: [fol_negation (CONJUNCTION fol_negation)* CONJUNCTION] fol_negation_quant -> fol_conjunction

?fol_disjunction: fol_conjunction (DISJUNCTION fol_conjunction)*
?fol_disjunction_quant: [fol_conjunction (DISJUNCTION fol_conjunction)* DISJUNCTION] fol_conjunction_quant -> fol_disjunction

?fol_implication: fol_disjunction (IMPLICATION fol_disjunction)*
?fol_implication_quant: [fol_disjunction (IMPLICATION fol_disjunction)* IMPLICATION] fol_disjunction_quant -> fol_implication

?fol_equivalence: [fol_implication EQUIVALENCE] fol_implication
                | [fol_implication EQUIVALENCE] fol_implication_quant -> fol_equivalence

?fol_formula: fol_equivalence

fol_quantification: FORALL variable variable* "." fol_formula -> universal_quantification
                  | EXISTS variable variable* "." fol_formula -> existential_quantification
"""

theory_parser = Lark(
    syntax,
    start="theory",
    parser="lalr",
    lexer="standard",
    propagate_positions=True,
)

print(theory_parser.parse(r"""
theory LIST extending INT SET
    sort S

    // hmm

    function f: S S S -> S
    constant c: S
    relation R: S S S

    /* wuu */

    fixpoint R(x) = forall x:S . x = x /\ x = y:S \/ not forall x:S . not x = x \/ not exists y:S. true

    assert forall x. R(x) /\ not R(x)
end
""".strip()))

# synthesize stuff in this language
# check if a finite model is a model of this theory?
