from typing import Iterable, Generator

import time

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
#     modal.Box(modal.Box(atom_p)),
#     modal.Disjunction(
#         modal.Box(atom_p),
#         atom_p,
#     ),
# ),

# complete axiom for symmetric frames
# formula_templates = modal.Implication(
#     atom_p,
#     modal.Box(modal.Diamond(atom_p)),
# ),

# complete axiom for euclidean frames
# formula_templates = modal.Implication(
#     modal.Diamond(atom_p),
#     modal.Box(modal.Diamond(atom_p)),
# ),

# complete axiom for transitive frames
# formula_templates = modal.Implication(
#     modal.Box(atom_p),
#     modal.Box(modal.Box(atom_p)),
# ),

# formula_templates = modal.Implication(
#     modal.Diamond(modal.Box(atom_p)),
#     modal.Box(modal.Diamond(atom_p)),
# ),

atom_p = modal.Atom("p")

canonical_axioms = {
    "REFLEXIVE": modal.Implication(
        modal.Box(atom_p),
        atom_p,
    ),

    "TRANSITIVE": modal.Implication(
        modal.Box(atom_p),
        modal.Box(modal.Box(atom_p)),
    ),

    "SYMMETRIC": modal.Implication(
        atom_p,
        modal.Box(modal.Diamond(atom_p)),
    ),

    "EUCLIDEAN": modal.Implication(
        modal.Diamond(atom_p),
        modal.Box(modal.Diamond(atom_p)),
    ),

    "FUNCTIONAL": modal.Implication(
        modal.Diamond(atom_p),
        modal.Box(atom_p),
    ),
    
    "SHIFT-REFLEXIVE": modal.Box(
        modal.Implication(
            modal.Box(atom_p),
            atom_p,
        ),
    ),

    "DENSE": modal.Implication(
        modal.Box(modal.Box(atom_p)),
        modal.Box(atom_p),
    ),

    "SERIAL": modal.Implication(
        modal.Box(atom_p),
        modal.Diamond(atom_p),
    ),

    "CONVERGENT": modal.Implication(
        modal.Diamond(modal.Box(atom_p)),
        modal.Box(modal.Diamond(atom_p)),
    ),

    # "RST":,

    # "K45":,

    # "KB5":,

    # "D4":,

    # "D5":,

    # "D45":,

    # "DB":,

    # "M4":,

    # "M5":,
}

def find_axioms_for_theory(atoms: Tuple[modal.Atom, ...], goal_theory: Theory, theory_name: str) -> None:
    true_formulas: List[modal.Formula] = []
    synthesizer = modal.ModalSynthesizer(theory_map["FRAME"].language, "W", "R")

    connectives = (
        modal.Connective(modal.Falsum, 0),
        modal.Connective(modal.Verum, 0),

        modal.Connective(modal.Implication, 2),
        modal.Connective(modal.Disjunction, 2),
        modal.Connective(modal.Conjunction, 2),
        modal.Connective(modal.Negation, 1),

        modal.Connective(modal.Box, 1),
        modal.Connective(modal.Diamond, 1),
    )

    begin = time.time()
    first = True

    for formula, counterexample in synthesizer.synthesize(
        (
            modal.ModalFormulaTemplate(atoms, connectives, 2),
            modal.ModalFormulaTemplate(atoms, connectives, 3),
        ),
        theory_map["FRAME"],
        goal_theory,
        debug=True,
        check_soundness=True,
        # use_negative_examples=True,
    ):
        if counterexample is None:
            true_formulas.append(formula)

            if first:
                # print(f"${modal_formula_to_latex(formula)}", end="", flush=True)
                first = False
            else:
                pass
                # print(f", {modal_formula_to_latex(formula)}", end="", flush=True)

    # print("$ & ", end="", flush=True)

    # if theory_name in canonical_axioms:
    #     print(f"${modal_formula_to_latex(canonical_axioms[theory_name])}$ & ", end="", flush=True)
    # else:
    #     print("& ", end="", flush=True)

    print(f"  - synthesis spent: {time.time() - begin}s")
    # print(f"{round(time.time() - begin, 2)}\;s & ", end="", flush=True)
    begin = time.time()

    # if len(true_formulas) != 0:
    #     axiomtization = true_formulas[0]
    #     for formula in true_formulas[1:][::-1]:
    #         axiomtization = modal.Conjunction(axiomtization, formula)

    #     try:
    #         synthesizer.check_completeness(goal_theory, axiomtization, blob_depth=0, timeout=300 * 1000, debug=False)
    #     except:
    #         print(f"  - completeness check failed")
    #         # print("- \\\\")
    #         pass
    #     else:
    #         print(f"  - completeness check spent: {time.time() - begin}s")
    #         # print(f"{round(time.time() - begin, 2)}\;s \\\\")


def fo_formula_to_latex(formula: Formula) -> str:
    formula_str = str(formula.strip_universal_quantifiers()) \
        .replace("forall", "\\forall") \
        .replace("exists", "\\exists") \
        .replace(":W", "") \
        .replace("/\\", "\\wedge") \
        .replace("¬", "\\neg") \
        .replace("\\/", "\\vee") \
        .replace("->", "\\rightarrow")

    if formula_str.startswith("("):
        formula_str = formula_str[1:-1]

    return formula_str


def modal_formula_to_latex(formula: modal.Formula) -> str:
    formula_str = str(formula) \
        .replace("□", "\\MBox") \
        .replace("◊", "\\MDiam") \
        .replace("p", "\\alpha") \
        .replace("∧", "\\wedge") \
        .replace("¬", "\\neg") \
        .replace("∨", "\\vee") \
        .replace("→", "\\rightarrow") \
        .replace("⊤", "\\top") \
        .replace("/\\", "\\wedge") \
        .replace("\\/", "\\vee") \
        .replace("⊥", "\\bot") \
        .replace("->", "\\rightarrow")

    if formula_str.startswith("("):
        formula_str = formula_str[1:-1]

    return formula_str


if __name__ == "__main__":
    for theory_name in theory_map:
        if theory_name != "FRAME":
            print(f"# synthesizing for theory {theory_name}")
            axiom, = tuple(theory_map[theory_name].get_axioms())
            # ({theory_name.lower().capitalize()}) 
            # print(f"${fo_formula_to_latex(axiom.formula)}$ & ", end="", flush=True)
            find_axioms_for_theory((modal.Atom("p"),), theory_map[theory_name], theory_name)
