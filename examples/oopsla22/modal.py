from typing import Iterable, Generator, Dict, Tuple, Optional
from dataclasses import dataclass

import os
import sys
import time
import pickle
import argparse

from synthesis import *
from synthesis import modal
from synthesis.utils.stopwatch import Stopwatch


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


# https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog
canonical_axioms: Dict[str, Tuple[Union[modal.Formula, str], ...]] = (lambda atom_p: {
    "REFLEXIVE": (modal.Implication(
        modal.Box(atom_p),
        atom_p,
    ),),

    "TRANSITIVE": (modal.Implication(
        modal.Box(atom_p),
        modal.Box(modal.Box(atom_p)),
    ),),

    "SYMMETRIC": (modal.Implication(
        atom_p,
        modal.Box(modal.Diamond(atom_p)),
    ),),

    "EUCLIDEAN": (modal.Implication(
        modal.Diamond(atom_p),
        modal.Box(modal.Diamond(atom_p)),
    ),),

    "FUNCTIONAL": (modal.Implication(
        modal.Diamond(atom_p),
        modal.Box(atom_p),
    ),),
    
    "SHIFT-REFLEXIVE": (modal.Box(
        modal.Implication(
            modal.Box(atom_p),
            atom_p,
        ),
    ),),

    "DENSE": (modal.Implication(
        modal.Box(modal.Box(atom_p)),
        modal.Box(atom_p),
    ),),

    "SERIAL": (modal.Implication(
        modal.Box(atom_p),
        modal.Diamond(atom_p),
    ),),

    "CONVERGENT": (modal.Implication(
        modal.Diamond(modal.Box(atom_p)),
        modal.Box(modal.Diamond(atom_p)),
    ),),

    "K45": ("TRANSITIVE", "EUCLIDEAN"),

    "KB5": ("SYMMETRIC", "EUCLIDEAN"),

    "D4": ("SERIAL", "TRANSITIVE"),

    "D5": ("SERIAL", "EUCLIDEAN"),

    "D45": ("SERIAL", "TRANSITIVE", "EUCLIDEAN"),

    "DB": ("SERIAL", "SYMMETRIC"),

    "M4": ("REFLEXIVE", "TRANSITIVE"),

    "M5": ("REFLEXIVE", "EUCLIDEAN"),
})(modal.Atom("p"))


@dataclass
class Result:
    """
    Synthesis/completeness result for a theory, including timing info
    """
    theory_name: str
    fo_theory: Theory
    synthesized_axioms: Tuple[modal.Formula, ...]

    # Axioms that were synthesized but failed the independence check
    # NOTE: in the mode where independence check is folded into synthesis,
    # this list is expected to be empty
    dependent_axioms: Tuple[modal.Formula, ...]

    # Axioms that were synthesized and passed the independence check
    # but found unsound (via either the soundness check or the counterexample check)
    unsound_axioms: Tuple[modal.Formula, ...]

    # Total amount of time spent in each component
    # (in seconds)
    stopwatch: Stopwatch


def find_axioms_for_theory(
    atoms: Tuple[modal.Atom, ...],
    goal_theory: Theory,
    theory_name: str,
    args: argparse.Namespace,
) -> Result:
    synthesized_axioms: List[modal.Formula] = []
    dependent_axioms: List[modal.Formula] = []
    unsound_axioms: List[modal.Formula] = []

    synthesizer = modal.ModalSynthesizer(theory_map["FRAME"].language, sort_world="W", transition_symbol="R")

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

    stopwatch = Stopwatch()

    for formula, formula_type in synthesizer.synthesize(
        (
            modal.ModalFormulaTemplate(atoms, connectives, 2),
            modal.ModalFormulaTemplate(atoms, connectives, 3),
        ),
        theory_map["FRAME"],
        goal_theory,
        use_positive_examples=not args.disable_counterexamples,
        separate_independence=args.separate_independence,
        check_soundness=True,
        stopwatch=stopwatch,
        # use_negative_examples=True,
    ):
        if formula_type == modal.FormulaResultType.SOUND_INDEPENDENT:
            print(formula)
            synthesized_axioms.append(formula)
        elif formula_type == modal.FormulaResultType.DEPENDENT:
            dependent_axioms.append(formula)
        elif formula_type == modal.FormulaResultType.COUNTEREXAMPLE or \
             formula_type == modal.FormulaResultType.UNSOUND:
            unsound_axioms.append(formula)
        else:
            assert False, f"unknown formula type {formula_type}"

    print(f"  - encoding spent: {stopwatch.get('encoding')}s")
    print(f"  - synthesis spent: {stopwatch.get('synthesis')}s")
    print(f"  - counterexample spent: {stopwatch.get('counterexample')}s")
    print(f"  - soundness spent: {stopwatch.get('soundness')}s")

    if len(synthesized_axioms) != 0:
        axiomtization = synthesized_axioms[0]
        for formula in synthesized_axioms[1:][::-1]:
            axiomtization = modal.Conjunction(axiomtization, formula)

        try:
            with stopwatch.time("completeness"):
                complete = synthesizer.check_completeness(goal_theory, axiomtization, blob_depth=0, timeout=300 * 1000)
        except:
            print(f"  - completeness check exception")
        else:
            if complete:
                print(f"  - completeness check passed, spent: {stopwatch.get('completeness')}s")
            else:
                print(f"  - completeness check failed, spent: {stopwatch.get('completeness')}s")

    return Result(
        theory_name=theory_name,
        fo_theory=goal_theory,
        synthesized_axioms=synthesized_axioms,
        dependent_axioms=(),
        unsound_axioms=(),
        stopwatch=stopwatch,
    )


def fo_formula_to_latex(formula: Formula) -> str:
    """
    Encode a first-order formula in LaTeX
    TODO: slightly hacky
    """

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
    """
    Encode a modal formula in LaTeX
    TODO: slightly hacky
    """

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


def output_latex_entry(result: Result) -> None:
    """
    Output one result entry in LaTeX
    """

    print(result)


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(
        dest="command",
        title="available commands",
        help="additional help",
        required=True,
    )

    # Run synthesis
    parser_synthesize = subparsers.add_parser("synthesize", help="Synthesize modal logic axioms")
    parser_synthesize.add_argument("--save", type=str, default=None, help="save results to a file")
    parser_synthesize.add_argument("--separate-independence", action="store_true", default=False, help="separate independence check from the synthesis query")
    parser_synthesize.add_argument("--disable-counterexamples", action="store_true", default=False, help="disable the use of counterexamples (i.e. do enumeration)")

    # Render results in LaTeX
    parser_show = subparsers.add_parser("show", help="Render the given results in LaTeX")
    parser_show.add_argument("saved", help="Saved (partial) result file")

    args = parser.parse_args()

    if args.command == "synthesize":
        results: List[Result] = []

        if args.save is not None and os.path.isfile(args.save):
            print(f"!!! overriding save file {args.save}")

        for theory_name in theory_map:
            if theory_name != "FRAME":
                print(f"# synthesizing for theory {theory_name}")
                result = find_axioms_for_theory(
                    (modal.Atom("p"),),
                    theory_map[theory_name],
                    theory_name,
                    args,
                )
                results.append(result)

                if args.save is not None:
                    with open(args.save, "wb") as save_file:
                        pickle.dump(tuple(results), save_file)

    elif args.command == "show":
        with open(args.saved, "rb") as save_file:
            results = pickle.load(save_file)
            
            for result in results:
                output_latex_entry(result)

    else:
        assert False, f"unknown command {args.command}"


if __name__ == "__main__":
    main()


