from __future__ import annotations

from typing import Mapping, Set, Tuple
from dataclasses import dataclass
from abc import ABC, abstractmethod, abstractstaticmethod

from synthesis.smt import smt
from synthesis.template import Template


Letter = int
Word = Tuple[Letter, ...]


class Pattern(Template["Pattern"], ABC):
    @abstractmethod
    def match(self, word: Word, valuation: Mapping[Variable, Pattern]) -> smt.SMTTerm: ...


@dataclass
class Constant(Pattern):
    word: Word

    def match(self, word: Word, valuation: Mapping[Variable, Pattern]) -> smt.SMTTerm:
        return smt.Bool(self == word)


@dataclass
class Variable(Pattern):
    name: str

    def match(self, word: Word, valuation: Mapping[Variable, Pattern]) -> smt.SMTTerm:
        assert self in valuation, f"variable {self} not found in valuation"
        return valuation[self].match(word, valuation)


@dataclass
class Union(Pattern):
    left: Pattern
    right: Pattern

    def match(self, word: Word, valuation: Mapping[Variable, Pattern]) -> smt.SMTTerm:
        return smt.Or(
            self.left.match(word, valuation),
            self.right.match(word, valuation),
        )


@dataclass
class Concat(Pattern):
    left: Pattern
    right: Pattern

    def match(self, word: Word, valuation: Mapping[Variable, Pattern]) -> smt.SMTTerm:
        """
        Non-deterministically find a split point
        """
        return smt.Or(
            smt.And(
                self.left.match(word[:i], valuation),
                self.right.match(word[i:], valuation),
            )
            for i in range(len(word) + 1)  
        )


@dataclass
class Closure(Pattern):
    pattern: Pattern

    def match(self, word: Word, valuation: Mapping[Variable, Pattern]) -> smt.SMTTerm:
        if len(word) == 0:
            return smt.TRUE()

        return smt.Or(
            smt.And(
                self.pattern.match(word[:i], valuation),
                self.match(word[i:], valuation),
            )
            for i in range(1, len(word) + 1)
        )
