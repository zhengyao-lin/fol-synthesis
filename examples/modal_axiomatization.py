from typing import Iterable, Generator

from synthesis import *
from synthesis import modal

theory_map = Parser.parse_theories(r"""
theory FRAME
    sort W
    relation R: W W
end

theory REFLEXIVE extending FRAME
    axiom forall x: W. R(x, x)
end

theory TRANSITIVE extending FRAME
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(y, z) -> R(x, z)
end

theory SYMMETRIC extending FRAME
    axiom forall x: W, y: W. R(x, y) -> R(y, x)
end

theory EUCLIDEAN extending FRAME
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y)
end

theory FUNCTIONAL extending FRAME
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(x, z) -> y = z
end

theory SHIFT-REFLEXIVE extending FRAME
    axiom forall x: W, y: W. R(x, y) -> R(y, y)
end

theory DENSE extending FRAME
    axiom forall x: W, y: W. R(x, y) -> exists z: W. R(x, z) /\ R(z, y)
end

theory SERIAL extending FRAME
    axiom forall x: W. exists y: W. R(x, y)
end

// can't check completeness
theory CONVERGENT extending FRAME
    axiom forall x: W, y: W, z: W. R(x, y) /\ R(x, z) -> exists w: W. R(y, w) /\ R(z, w)
end

theory RST extending FRAME
    axiom forall x: W, y: W, z: W. R(x, x) /\ (R(x, y) -> R(y, x)) /\ (R(x, y) /\ R(y, z) -> R(x, z))
end

// can't check completeness
theory K45 extending FRAME
    axiom forall x: W, y: W, z: W. (R(x, y) /\ R(y, z) -> R(x, z)) /\ (R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y))
end

theory KB5 extending FRAME
    axiom forall x: W, y: W, z: W. (R(x, y) -> R(y, x)) /\ (R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y))
end

theory D4 extending FRAME
    axiom forall x: W, y: W, z: W. (R(x, y) /\ R(y, z) -> R(x, z)) /\ exists w: W. R(x, w)
end

// can't check completeness
theory D5 extending FRAME
    axiom forall x: W, y: W, z: W. (R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y)) /\ exists w: W. R(x, w)
end

// can't check completeness
theory D45 extending FRAME
    axiom forall x: W, y: W, z: W. (R(x, y) /\ R(y, z) -> R(x, z)) /\ (R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y)) /\ exists w: W. R(x, w)
end

theory DB extending FRAME
    axiom forall x: W, y: W, z: W. (R(x, y) -> R(y, x)) /\ exists w: W. R(x, w)
end

theory M4 extending FRAME
    axiom forall x: W, y: W, z: W. R(x, x) /\ (R(x, y) /\ R(y, z) -> R(x, z))
end

theory M5 extending FRAME
    axiom forall x: W, y: W, z: W. R(x, x) /\ (R(x, y) /\ R(x, z) -> R(y, z) /\ R(z, y))
end
""")

# true in symmetric frames but not complete
# formula_templates = modal.Implication(
#     modal.Modality(modal.Modality(atom_p)),
#     modal.Disjunction(
#         modal.Modality(atom_p),
#         atom_p,
#     ),
# ),

# complete axiom for symmetric frames
# formula_templates = modal.Implication(
#     atom_p,
#     modal.Modality(modal.Diamond(atom_p)),
# ),

# complete axiom for euclidean frames
# formula_templates = modal.Implication(
#     modal.Diamond(atom_p),
#     modal.Modality(modal.Diamond(atom_p)),
# ),

# complete axiom for transitive frames
# formula_templates = modal.Implication(
#     modal.Modality(atom_p),
#     modal.Modality(modal.Modality(atom_p)),
# ),

atoms = (
    modal.Atom("p"),
)

goal_theory = theory_map["M4"]

true_formulas: List[modal.Formula] = []
synthesizer = modal.ModalSynthesizer(theory_map["FRAME"].language, "W", "R")

for formula in synthesizer.synthesize(
    (
        modal.ModalFormulaTemplate(atoms, 2),
        modal.ModalFormulaTemplate(atoms, 3),
        # modal.ModalFormulaTemplate(atoms, 4),
    ),
    theory_map["FRAME"],
    goal_theory,
):
    true_formulas.append(formula)

if len(true_formulas) != 0:
    axiomtization = true_formulas[0]
    for formula in true_formulas[1:][::-1]:
        axiomtization = modal.Conjunction(axiomtization, formula)

    synthesizer.check_completeness(goal_theory, axiomtization)
