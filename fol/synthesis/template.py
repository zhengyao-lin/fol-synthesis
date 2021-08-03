from typing import TypeVar, Generic, Iterable, Tuple

from abc import ABC, abstractmethod

from fol.smt import smt


T = TypeVar("T")


class Template(Generic[T], ABC):
    """
    Template[T] is a variable/constant in SMT that represents a value of T
    """

    @abstractmethod
    def get_constraint(self) -> smt.SMTTerm: ...

    @abstractmethod
    def equals(self, value: T) -> smt.SMTTerm: ...

    @abstractmethod
    def get_from_smt_model(self, model: smt.SMTModel) -> T: ...


class BoundedIntegerVariable(Template[int]):
    """
    An integer variable with range lower upper
    """

    def __init__(self, lower: int, upper: int):
        assert upper >= lower
        self.lower = lower
        self.upper = upper
        self.variable = smt.FreshSymbol(smt.INT)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.And(smt.LE(smt.Int(self.lower), self.variable), smt.LE(self.variable, smt.Int(self.upper)))

    def get_from_smt_model(self, model: smt.SMTModel) -> int:
        return model[self.variable].constant_value() # type: ignore

    def equals(self, value: int) -> smt.SMTTerm:
        return smt.Equals(self.variable, smt.Int(value))

    def get_range(self) -> Iterable[int]:
        return range(self.lower, self.upper + 1)
