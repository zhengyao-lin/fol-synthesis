from typing import Iterable, Generator, Dict, Tuple, Optional
from dataclasses import dataclass

import os
import sys
import time
import pickle
import random
import argparse
import itertools
import traceback
import multiprocessing

import matplotlib

matplotlib.rcParams.update({
    "font.size": 22,
    "text.usetex": True,
    "text.latex.preamble": [
        r"""
        \usepackage[libertine]{newtxmath}
        \usepackage{libertine}
        """
    ],
})

import matplotlib.pyplot as plot

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


@dataclass
class ModalLogicInfo:
    # Mapping the theory name to more info about the logic/theory
    display_name: Optional[str]
    acronym: str
    canonical_axioms: Optional[Tuple[modal.Formula, ...]]
    combination: Optional[Tuple[str, ...]] # optionally define the theory as the combination of others


# https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog
modal_logic_info: Tuple[Tuple[str, ModalLogicInfo], ...] = (lambda atom_p: [
    ("REFLEXIVE", ModalLogicInfo(
        "Reflexive",
        "(M)",
        (modal.Implication(
            modal.Box(atom_p),
            atom_p,
        ),),
        None,
    )),

    ("TRANSITIVE", ModalLogicInfo(
        "Transitive",
        "(4)",
        (modal.Implication(
            modal.Box(atom_p),
            modal.Box(modal.Box(atom_p)),
        ),),
        None,
    )),

    ("SYMMETRIC", ModalLogicInfo(
        "Symmetric",
        "(B)",
        (modal.Implication(
            atom_p,
            modal.Box(modal.Diamond(atom_p)),
        ),),
        None,
    )),

    ("EUCLIDEAN", ModalLogicInfo(
        "Euclidean",
        "(5)",
        (modal.Implication(
            modal.Diamond(atom_p),
            modal.Box(modal.Diamond(atom_p)),
        ),),
        None,
    )),
    
    ("SHIFT-REFLEXIVE", ModalLogicInfo(
        "Shift Reflexive",
        "($\\square$M)",
        (modal.Box(modal.Implication(
            modal.Box(atom_p),
            atom_p,
        )),),
        None,
    )),

    ("SERIAL", ModalLogicInfo(
        "Serial",
        "(D)",
        (modal.Implication(
            modal.Box(atom_p),
            modal.Diamond(atom_p),
        ),),
        None,
    )),

    ("CONVERGENT", ModalLogicInfo(
        "Convergent",
        "(C)",
        (modal.Implication(
            modal.Diamond(modal.Box(atom_p)),
            modal.Box(modal.Diamond(atom_p)),
        ),),
        None,
    )),

    ("FUNCTIONAL", ModalLogicInfo(
        "Functional",
        "(CD)",
        (modal.Implication(
            modal.Diamond(atom_p),
            modal.Box(atom_p),
        ),),
        None, # ("CONVERGENT", "SERIAL"),
    )),

    ("DENSE", ModalLogicInfo(
        "Dense",
        "(C4)",
        (modal.Implication(
            modal.Box(modal.Box(atom_p)),
            modal.Box(atom_p),
        ),),
        None, # ("CONVERGENT", "TRANSITIVE"),
    )),

    ("K45", ModalLogicInfo(None, "(K45)", None, ("TRANSITIVE", "EUCLIDEAN"))),

    ("KB5", ModalLogicInfo(None, "(KB5)", None, ("SYMMETRIC", "EUCLIDEAN"))),

    ("D4", ModalLogicInfo(None, "(D4)", None, ("SERIAL", "TRANSITIVE"))),

    ("D5", ModalLogicInfo(None, "(D5)", None, ("SERIAL", "EUCLIDEAN"))),

    ("D45", ModalLogicInfo(None, "(D45)", None, ("SERIAL", "TRANSITIVE", "EUCLIDEAN"))),

    ("DB", ModalLogicInfo(None, "(DB)", None, ("SERIAL", "SYMMETRIC"))),

    ("M4", ModalLogicInfo(None, "(M4)", None, ("REFLEXIVE", "TRANSITIVE"))),

    ("M5", ModalLogicInfo(None, "(M5)", None, ("REFLEXIVE", "EUCLIDEAN"))),
])(modal.Atom("p"))


@dataclass
class SynthesizedFormula:
    """
    A formula with some additional info:
    - the time it was synthesized
    - the formula result type
    """

    formula: modal.Formula
    result: modal.FormulaResultType
    time: float # in seconds


@dataclass
class Result:
    """
    Synthesis/completeness result for a theory, including timing info
    """
    theory_name: str
    fo_theory: Theory

    complete: bool # if the completeness check succeeded

    synthesized_axioms: Tuple[SynthesizedFormula, ...]

    # Total amount of time took in each component
    # (in seconds)
    stopwatch: Stopwatch


def find_axioms_for_theory(
    args: argparse.Namespace,
    atoms: Tuple[modal.Atom, ...],
    goal_theory: Theory,
    theory_name: str,
) -> Result:
    synthesizer = modal.ModalSynthesizer(
        theory_map["FRAME"].language,
        sort_world="W",
        transition_symbol="R",
        solver_seed=args.seed,
        output=sys.stderr if args.debug else open(os.devnull, "w"),
    )

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

    # Try formulas with depths 1, 2, and 3 in sequence
    templates = (
        modal.ModalFormulaTemplate(atoms, connectives, 1),
        modal.ModalFormulaTemplate(atoms, connectives, 2),
        modal.ModalFormulaTemplate(atoms, connectives, 3),
    )

    stopwatch = Stopwatch()
    synthesized_axioms: List[SynthesizedFormula] = []

    stopwatch.start("synthesis-total")

    for formula, formula_type in synthesizer.synthesize(
        templates,
        theory_map["FRAME"],
        goal_theory,
        use_positive_examples=not args.disable_counterexamples,
        separate_independence=args.separate_independence,
        use_enumeration=args.use_enumeration,
        model_size_bound=args.model_size_bound,
        check_soundness=True,
        stopwatch=stopwatch,
        # use_negative_examples=True,
    ):
        synthesized_axioms.append(SynthesizedFormula(
            formula=formula,
            result=formula_type,
            time=stopwatch.get("synthesis-total"),
        ))

        if formula_type == modal.FormulaResultType.GOOD:
            print(formula)

    stopwatch.end("synthesis-total")

    # print(f"- encoding took: {stopwatch.get('encoding')}s")
    # print(f"- synthesis took: {stopwatch.get('synthesis')}s")
    # print(f"- counterexample took: {stopwatch.get('counterexample')}s")
    # print(f"- soundness took: {stopwatch.get('soundness')}s")

    # prune dependent axioms in synthesized_axioms
    # NOTE: this may have false positives (i.e. independent axioms might be pruned)
    good_axioms: List[SynthesizedFormula] = [
        axiom
        for axiom in synthesized_axioms
        if axiom.result == modal.FormulaResultType.GOOD
    ]
    indep_axioms: List[modal.Formula] = []

    with stopwatch.time("pruning"):
        while len(good_axioms) != 0:
            goal = good_axioms.pop(0)
            axioms = indep_axioms + [ axiom.formula for axiom in good_axioms ]

            if not synthesizer.check_modal_entailment(
                axioms,
                goal.formula,
                model_size_bound=args.model_size_bound,
            ):
                indep_axioms.append(goal.formula)
            else:
                goal.result = modal.FormulaResultType.PRUNED
                # print(f"pruned possibly dependent axiom {goal.formula}")

    # print(f"- pruning took: {stopwatch.get('pruning')}s")

    # check completeness
    if len(indep_axioms) != 0:
        as_one_axiom = indep_axioms[0]
        for formula in indep_axioms[1:][::-1]:
            as_one_axiom = modal.Conjunction(as_one_axiom, formula)

        try:
            with stopwatch.time("completeness"):
                complete = synthesizer.check_completeness(
                    goal_theory,
                    as_one_axiom,
                    blob_depth=0,
                    timeout=args.completeness_timeout,
                )
        except:
            # print("- completeness check exception")
            complete = False
        else:
            pass
            # if complete:
            #     print(f"- completeness check passed, took: {stopwatch.get('completeness')}s")
            # else:
            #     print(f"- completeness check failed, took: {stopwatch.get('completeness')}s")

    return Result(
        theory_name=theory_name,
        fo_theory=goal_theory,
        complete=complete,
        synthesized_axioms=synthesized_axioms,
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


def synthesis_job(args: argparse.Namespace, queue: multiprocessing.Queue, theory_name: str) -> None:
    # def job() -> None:
    smt.reset()
    # print()
    print(f"synthesizing for theory {theory_name}")
    result = find_axioms_for_theory(
        args,
        (modal.Atom("p"),),
        theory_map[theory_name],
        theory_name,
    )
    queue.put(result)

    # make an extra fork each time to reset any global state
    # proc = multiprocessing.Process(target=job)
    # proc.start()
    # proc.join()


def write_result_job(args: argparse.Namespace, queue: multiprocessing.Queue) -> None:
    if args.save is None:
        return

    results: List[Result] = []

    while True:
        result = queue.get()
        if result is None: break

        print(f"synthesis for {result.theory_name} finished")

        results.append(result)

        with open(args.save, "wb") as save_file:
            pickle.dump(tuple(results), save_file)


def command_synthesize(args: argparse.Namespace) -> None:
    result_queue = multiprocessing.Manager().Queue()
    skip_theories: Set[str] = set()

    if args.save is not None and os.path.isfile(args.save) and not args.cont:
        print(f"overriding save file {args.save}")

    if args.cont:
        assert args.save is not None, "no save file provided for --continue"

        if os.path.isfile(args.save):
            with open(args.save, "rb") as save_file:
                for result in pickle.load(save_file):
                    # print(f"# skipping theory {result.theory_name}")
                    skip_theories.add(result.theory_name)
                    result_queue.put(result)

    # start a process to write results to the save file
    multiprocessing.Process(target=write_result_job, args=(args, result_queue), daemon=True).start()

    if args.logics is not None:
        for logic in args.logics:
            assert logic in theory_map, f"theory {logic} is not found"

    with multiprocessing.Pool(processes=args.jobs) as pool:
        pool.starmap(
            synthesis_job,
            [
                (args, result_queue, name)
                for name in theory_map
                if name not in skip_theories and
                   name != "FRAME" and
                   (args.logics is None or name in args.logics)
            ],
        )

    result_queue.put(None)


def round_str(num: int, round_to: int = 0) -> str:
    s = str(round(num, round_to))
    split = s.split(".")
    if len(split) == 2 and split[1]:
        return s + "0" * (round_to - len(split[1]))
    
    elif len(split) == 1 and round_to > 0:
        return s + "." + "0" * round_to

    return s


def output_latex_table(results: Tuple[Result, ...]) -> None:
    result_map: Dict[str, Result] = { result.theory_name: result for result in results }
    rows: List[str] = []

    for theory_name, theory in modal_logic_info:
        if theory_name not in result_map:
            continue

        result = result_map[theory_name]

        # if theory.display_name is not None:
        #     rows.append(r"{\bf " + theory.display_name + r"}")
        # else:
        #     rows.append(r"\vspace*{0.1cm}")

        # first_row_prefix = f"~~{theory.acronym}"

        first_row_prefix = theory.acronym

        # if theory.display_name is not None:
        #     first_row_prefix = f"{theory.acronym} = {theory.display_name}"
        # else:
        #     first_row_prefix = f"{theory.acronym}"
        
        if theory.display_name is not None:
            # use the first-order definition
            first_row_prefix += f" & {theory.display_name}"
            # first_row_prefix += " $" + fo_formula_to_latex(theory_map[theory_name].axioms[0].formula) + "$"
        elif theory.combination is not None:
            # e.g. = (C) + (D)
            acronyms = (dict(modal_logic_info)[name].acronym for name in theory.combination)
            first_row_prefix += " & " + " + ".join(acronyms)
        else:
            assert False, f"no first-order description of {theory_name} given"

        first_row_prefix += " &"

        # total = result.stopwatch.get("synthesis") + result.stopwatch.get("counterexample") + result.stopwatch.get("soundness") + result.stopwatch.get("completeness")
        # print(result.stopwatch.get("synthesis") / total, file=sys.stderr)

        synthesis_time = round_str(result.stopwatch.get("synthesis") + result.stopwatch.get("encoding"), 1)
        counterexample_time = round_str(result.stopwatch.get("counterexample"), 2)
        soundness_time = round_str(result.stopwatch.get("soundness"), 2)
        completeness_time = round_str(result.stopwatch.get("completeness"), 2) if result.complete else "timeout"
        first_row_suffix = f" & {synthesis_time} & {counterexample_time} & {soundness_time} & {completeness_time}"

        other_row_prefix = "& &"
        other_row_suffix = ""

        # reference modal axioms
        if theory.canonical_axioms is not None:
            reference = theory.canonical_axioms
        else:
            reference = sum(tuple(dict(modal_logic_info)[name].canonical_axioms for name in theory.combination), start=())

        # synthesized modal axioms
        # NOTE: formula is simplified here
        synthesized = tuple(axiom.formula.simplify() for axiom in result.synthesized_axioms if axiom.result == modal.FormulaResultType.GOOD)

        for i, (left, right) in enumerate(itertools.zip_longest(synthesized, reference)):
            if i == 0:
                row = first_row_prefix
            else:
                row = other_row_prefix

            if left is not None:
                row += f" ${modal_formula_to_latex(left)}$"
            row += " &"

            if right is not None:
                row += f" ${modal_formula_to_latex(right)}$"

            if i == 0:
                row += first_row_suffix
            else:
                row += other_row_suffix

            rows.append(row)

    for row in rows:
        print(f"{row} \\\\")


def output_summary(results: Tuple[Result, ...]) -> None:
    for result in results:
        print(f"{result.theory_name} theory:")
        for axiom in result.synthesized_axioms:
            print(f"  {axiom.formula} (i.e. {axiom.formula.simplify()}): {axiom.result}")

        print(f"  completeness check: {'passed' if result.complete else 'failed'}")

        for name, elapsed in result.stopwatch.get_all().items():
            print(f"  {name} took: {round(elapsed, 2)}s")


def output_timing_graph(args: argparse.Namespace, results: Tuple[Result, ...]) -> None:
    result_map: Dict[str, Result] = { result.theory_name: result for result in results }

    # theory_names = tuple(map(lambda t: f"{t[1].display_name + ' ' if t[1].display_name is not None else ''}{t[1].acronym}", modal_logic_info))
    theory_names = tuple(map(lambda t: t[1].acronym, modal_logic_info))

    plot.figure(figsize=(14, 8))

    plot.xlabel("Time (seconds)")
    # plot.ylabel("Modal Logic")
    plot.yticks(range(len(modal_logic_info)), reversed(theory_names))
    # plot.xscale("log")

    marker_map: Dict[modal.FormulaResultType, Mapping[str, str]] = {
        modal.FormulaResultType.GOOD: { "marker": "o", "color": "green", "markersize": 7 },
        modal.FormulaResultType.COUNTEREXAMPLE: { "marker": 2, "color": "red", "markersize": 7 },
        modal.FormulaResultType.UNSOUND: { "marker": 2, "color": "red", "markersize": 7 },
        modal.FormulaResultType.DEPENDENT: { "marker": 3, "color": "blue", "markersize": 7 },
        modal.FormulaResultType.PRUNED: { "marker": 3, "color": "blue", "markersize": 7 },
    }

    point_label: Dict[modal.FormulaResultType, str] = {
        modal.FormulaResultType.GOOD: "Good",
        modal.FormulaResultType.COUNTEREXAMPLE: "Unsound",
        modal.FormulaResultType.UNSOUND: "Unsound",
        modal.FormulaResultType.DEPENDENT: "Dependent",
        modal.FormulaResultType.PRUNED: "Dependent",
    }

    # if a point of a given label have been plotted
    existing_labels: Dict[str, None] = {}

    max_synthesis_time = 0

    for i, (theory_name, t) in enumerate(reversed(modal_logic_info)):
        if theory_name not in result_map:
            continue

        result = result_map[theory_name]

        synthesis_time = result.stopwatch.get("synthesis-total")
        max_synthesis_time = max(max_synthesis_time, synthesis_time)

        plot.plot([ 0, synthesis_time ], [ i, i ], color="black")
        plot.plot([ synthesis_time ], [ i ], marker="|", color="black")
        # plot.plot([ result.stopwatch.get("synthesis") + result.stopwatch.get("encoding") + result.stopwatch.get("soundness") + result.stopwatch.get("counterexample") ], [ i ], marker="1", color="black")

        for axiom in result.synthesized_axioms:
            if axiom.result in marker_map and axiom.result in point_label:
                label = point_label[axiom.result]
                if label in existing_labels:
                    label = None
                else:
                    existing_labels[label] = None

                plot.plot([ axiom.time ], [ i ], **marker_map[axiom.result], label=label)
            else:
                print(f"result type {axiom.result} not found")

    plot.legend()
    plot.xlim(-0.2, 20) # max_synthesis_time + 1)
    plot.tight_layout()

    if args.save_plot is not None:
        plot.savefig(args.save_plot)
    else:
        plot.show()


def command_show(args: argparse.Namespace) -> None:
    """
    Output one result entry in LaTeX
    """
    with open(args.saved, "rb") as save_file:
        results = pickle.load(save_file)

    output_latex_table(results)
    # output_summary(results)
    output_timing_graph(args, results)


def command_diff(args: argparse.Namespace) -> None:
    with open(args.first, "rb") as saved_first, \
         open(args.second, "rb") as saved_second:
        results_first = { result.theory_name: result for result in pickle.load(saved_first) }
        results_second = { result.theory_name: result for result in pickle.load(saved_second) }

    for theory_name, _ in modal_logic_info:
        if theory_name in results_first and theory_name not in results_second:
            print(f"theory {theory_name} in {args.first} but not in {args.second}")
        
        elif theory_name not in results_first and theory_name in results_second:
            print(f"theory {theory_name} in {args.second} but not in {args.first}")

        elif theory_name not in results_first and theory_name not in results_second:
            print(f"theory {theory_name} not found in both save files")
        
        else:
            result_first = results_first[theory_name]
            result_second = results_second[theory_name]
            axioms_first = set(((axiom.formula, axiom.result) for axiom in result_first.synthesized_axioms))
            axioms_second = set(((axiom.formula, axiom.result) for axiom in result_second.synthesized_axioms))

            if axioms_first != axioms_second:
                print(f"theory {theory_name} have different synthesis results")
            elif result_first.complete != result_second.complete:
                print(f"theory {theory_name} have different completeness results")
            else:
                print(f"theory {theory_name} have the same results")


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(
        dest="command",
        title="available commands",
        help="additional help",
        required=True,
    )

    # Run synthesis
    parser_synthesize = subparsers.add_parser("synthesize", help="synthesize modal logic axioms")
    parser_synthesize.add_argument("logics", nargs="*", help="synthesize for only specific logics")
    parser_synthesize.add_argument("--continue", dest="cont", action="store_true", default=False, help="skip re-synthesizing existing results in the save file")
    parser_synthesize.add_argument("--debug", action="store_true", default=False, help="enable debug output from the synthesizer")
    parser_synthesize.add_argument("-j", "--jobs", dest="jobs", type=int, default=1, help="number of parallel processes to perform synthesis")
    parser_synthesize.add_argument("-s", "--seed", dest="seed", type=int, default=0, help="random seed given to the SMT solver")
    parser_synthesize.add_argument("--save", type=str, default=None, help="save results to a file")
    parser_synthesize.add_argument("--model-size-bound", type=int, default=4, help="size bound of counterexample models/frames")
    parser_synthesize.add_argument("--completeness-timeout", type=int, default=300 * 1000, help="completeness check timeout in ms")
    parser_synthesize.add_argument("--use-enumeration", action="store_true", default=False, help="use an enumerative synthesizer")
    parser_synthesize.add_argument("--separate-independence", action="store_true", default=False, help="separate independence check from the synthesis query")
    parser_synthesize.add_argument("--disable-counterexamples", action="store_true", default=False, help="disable the use of counterexamples (i.e. do enumeration)")

    # Render results in LaTeX
    parser_show = subparsers.add_parser("show", help="render the given results in LaTeX")
    parser_show.add_argument("saved", help="saved (partial) result file")
    parser_show.add_argument("--save-plot", type=str, default=None, help="save path of the plot")

    # Compare difference in two results
    parser_diff = subparsers.add_parser("diff", help="Show the difference between two runs")
    parser_diff.add_argument("first", help="first save file")
    parser_diff.add_argument("second", help="second save file")

    args = parser.parse_args()

    if args.command == "synthesize":
        command_synthesize(args)

    elif args.command == "show":
        command_show(args)
    
    elif args.command == "diff":
        command_diff(args)

    else:
        assert False, f"unknown command {args.command}"


if __name__ == "__main__":
    main()
