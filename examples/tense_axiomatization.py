from typing import Iterable, Generator

from synthesis import *
from synthesis import modal

theory_map = Parser.parse_theories(r"""
theory FRAME
    sort W
    relation R: W W
end

theory IRREFLEXIVE extending FRAME
    axiom exists x: W. not R(x, x)
end

theory REFLEXIVE extending FRAME
    axiom forall x: W. R(x, x)
end

theory LIN extending FRAME
    axiom forall x: W, y: W. R(x, y) \/ x = y \/ R(y, x)
    // axiom forall x: W, y: W, z: W. R(x, y) /\ R(y, z) -> R(x, z)
    // axiom exists x: W. not R(x, x)
end
""")

atoms = (
    modal.Atom("p"),
)

goal_theory = theory_map["LIN"]

true_formulas: List[modal.Formula] = []
synthesizer = modal.ModalSynthesizer(theory_map["FRAME"].language, "W", "R")

connectives = (
    # modal.Connective(modal.Implication, 2),
    # modal.Connective(modal.Box, 1),
    # modal.Connective(modal.Diamond, 1),
    # modal.Connective(modal.Disjunction, 2),
    # modal.Connective(modal.Conjunction, 2),
    # modal.Connective(modal.Negation, 1),

    modal.Connective(modal.Implication, 2),
    modal.Connective(modal.Disjunction, 2),

    modal.Connective(modal.Diamond, 1),
    modal.Connective(modal.DiamondPast, 1),

    modal.Connective(lambda phi: modal.Diamond(modal.DiamondPast(phi)), 1),
    modal.Connective(lambda phi: modal.DiamondPast(modal.Diamond(phi)), 1),
)

for formula in synthesizer.synthesize(
    (
        # modal.ModalFormulaTemplate(atoms, connectives, 2),
        modal.Implication(
            modal.Disjunction(
                modal.Diamond(modal.DiamondPast(atoms[0])),
                modal.DiamondPast(modal.Diamond(atoms[0])),
            ),
            modal.Disjunction(
                modal.DiamondPast(atoms[0]),
                modal.Disjunction(
                    modal.Diamond(atoms[0]),
                    atoms[0],
                ),
            ),
        ),
    ),
    theory_map["FRAME"],
    goal_theory,
    model_size_bound=3,
):
    true_formulas.append(formula)

if len(true_formulas) != 0:
    axiomtization = true_formulas[0]
    for formula in true_formulas[1:][::-1]:
        axiomtization = modal.Conjunction(axiomtization, formula)

    synthesizer.check_completeness(goal_theory, axiomtization)
