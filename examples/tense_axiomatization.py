from typing import Iterable, Generator

from synthesis import *
from synthesis import modal

theory_map = Parser.parse_theories(r"""
theory FRAME
    sort W
    relation R: W W
end

theory IRREFLEXIVE extending FRAME
    axiom forall x: W. not R(x, x)
end

theory REFLEXIVE extending FRAME
    axiom forall x: W. R(x, x)
end

theory TRANSITIVE extending FRAME
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(y, z) -> R(x, z)
end

theory LIN-F extending FRAME
    axiom forall x: W, y: W, z: W. R(z, x) /\ R(z, y) -> R(x, y) \/ x = y \/ R(y, x)
end

theory LIN-B extending FRAME
    axiom forall x: W, y: W, z: W. R(x, z) /\ R(y, z) -> R(x, y) \/ x = y \/ R(y, x)
end

theory LIN extending FRAME
    axiom forall x: W, y: W. R(x, y) \/ x = y \/ R(y, x)
end

// 5.088s
// modal.ModalFormulaTemplate((), connectives, 3)
theory BEG extending IRREFLEXIVE TRANSITIVE
    axiom exists x: W. forall y: W. not R(y, x)
end

// 5.724s
// modal.ModalFormulaTemplate((), connectives, 3)
theory END extending IRREFLEXIVE TRANSITIVE
    axiom exists x: W. forall y: W. not R(x, y)
end

// 4.087s
// modal.ModalFormulaTemplate((), connectives, 3)
theory NOBEG extending FRAME
    axiom forall x: W. exists y: W. R(y, x)
end

// 4.252s
// modal.ModalFormulaTemplate((), connectives, 3)
theory NOEND extending FRAME
    axiom forall x: W. exists y: W. R(x, y)
end

theory DISCR-F extending LIN
    axiom forall x: W, y: W. R(x, y) -> exists z: W. R(x, z) /\ (z = y \/ R(z, y)) /\ not exists u: W. R(x, u) /\ R(u, z)
end

theory DISCR-B extending LIN
    axiom forall x: W, y: W. R(y, x) -> exists z: W. R(z, x) /\ (y = z \/ R(y, z)) /\ not exists u: W. R(z, u) /\ R(u, x)
end
""")

atoms = (
    modal.Atom("p"),
)

goal_theory = theory_map["NOBEG"]

true_formulas: List[modal.Formula] = []
synthesizer = modal.ModalSynthesizer(theory_map["FRAME"].language, "W", "R")

connectives = (
    modal.Connective(modal.Falsum, 0),
    # modal.Connective(modal.Verum, 0),

    modal.Connective(modal.Implication, 2),
    modal.Connective(modal.Disjunction, 2),
    # modal.Connective(lambda a, b, c: modal.Disjunction(a, modal.Disjunction(b, c)), 3),
    modal.Connective(modal.Conjunction, 2),
    modal.Connective(modal.Negation, 1),

    modal.Connective(modal.Box, 1),
    modal.Connective(modal.BoxPast, 1),
    modal.Connective(modal.Diamond, 1),
    modal.Connective(modal.DiamondPast, 1),

    # modal.Connective(lambda phi: modal.Diamond(modal.BoxPast(phi)), 1),
    # modal.Connective(lambda phi: modal.Diamond(modal.DiamondPast(phi)), 1),
    # modal.Connective(lambda phi: modal.DiamondPast(modal.Diamond(phi)), 1),
)

for formula, counterexample in synthesizer.synthesize(
    (
        modal.ModalFormulaTemplate(atoms, connectives, 1),
        modal.ModalFormulaTemplate(atoms, connectives, 2),
        modal.ModalFormulaTemplate(atoms, connectives, 3),
        # modal.ModalFormulaTemplate((), connectives, 3),
        # modal.Disjunction(
        #     modal.BoxPast(modal.Falsum()),
        #     modal.DiamondPast(modal.BoxPast(modal.Falsum())),
        # ),
    ),
    theory_map["FRAME"],
    goal_theory,
    model_size_bound=4,
    # use_negative_examples=True,
    # debug=False,
    check_soundness=True,
):
    if counterexample is None:
        true_formulas.append(formula)

if len(true_formulas) != 0:
    axiomtization = true_formulas[0]
    for formula in true_formulas[1:][::-1]:
        axiomtization = modal.Conjunction(axiomtization, formula)
    synthesizer.check_completeness(goal_theory, axiomtization, blob_depth=0, timeout=300 * 1000)

# LIN
# modal.Implication(
#     modal.Disjunction(
#         modal.Diamond(modal.DiamondPast(atoms[0])),
#         modal.DiamondPast(modal.Diamond(atoms[0])),
#     ),
#     modal.Disjunction(
#         modal.DiamondPast(atoms[0]),
#         modal.Disjunction(
#             modal.Diamond(atoms[0]),
#             atoms[0],
#         ),
#     ),
# ),

# LIN-F
# modal.Implication(
#     modal.DiamondPast(modal.Diamond(atoms[0])),
#     modal.Disjunction(
#         modal.DiamondPast(atoms[0]),
#         modal.Disjunction(
#             modal.Diamond(atoms[0]),
#             atoms[0],
#         ),
#     ),
# ),

# LIN-B
# modal.Implication(
#     modal.Diamond(modal.DiamondPast(atoms[0])),
#     modal.Disjunction(
#         modal.DiamondPast(atoms[0]),
#         modal.Disjunction(
#             modal.Diamond(atoms[0]),
#             atoms[0],
#         ),
#     ),
# ),

# DISCR-F
# modal.Implication(
#     modal.Conjunction(
#         modal.Diamond(modal.Verum()),
#         modal.Conjunction(
#             atoms[0],
#             modal.BoxPast(atoms[0]),
#         ),
#     ),
#     modal.Diamond(modal.BoxPast(atoms[0])),
# ),

# DISCR-B
# modal.Implication(
#     modal.Conjunction(
#         modal.DiamondPast(modal.Verum()),
#         modal.Conjunction(
#             atoms[0],
#             modal.Box(atoms[0]),
#         ),
#     ),
#     modal.DiamondPast(modal.Box(atoms[0])),
# ),
