from typing import Dict
from abc import ABC, abstractmethod
from dataclasses import dataclass

from synthesis.smt import smt

import synthesis.fol as fol


class Frame(ABC):
    @abstractmethod
    def get_smt_sort(self) -> smt.SMTSort: ...

    def get_fresh_constant(self) -> smt.SMTTerm:
        return smt.FreshSymbol(self.get_smt_sort())

    @abstractmethod
    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...

    @abstractmethod
    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm: ...

    @abstractmethod
    def interpret_transition(self, from_world: smt.SMTTerm, to_world: smt.SMTTerm) -> smt.SMTTerm:
        """
        Return a constraint saying that the from_world transitions to the to_world
        """
        ...


@dataclass
class FOStructureFrame(Frame):
    structure: fol.Structure
    world_sort: fol.Sort
    transition_symbol: fol.RelationSymbol

    def get_smt_sort(self) -> smt.SMTSort:
        return self.structure.get_smt_sort(self.world_sort)

    def universally_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        carrier = self.structure.interpret_sort(self.world_sort)
        return carrier.universally_quantify(variable, formula)

    def existentially_quantify(self, variable: smt.SMTVariable, formula: smt.SMTTerm) -> smt.SMTTerm:
        carrier = self.structure.interpret_sort(self.world_sort)
        return carrier.existentially_quantify(variable, formula)

    def interpret_transition(self, from_world: smt.SMTTerm, to_world: smt.SMTTerm) -> smt.SMTTerm:
        return self.structure.interpret_relation(self.transition_symbol, from_world, to_world)
