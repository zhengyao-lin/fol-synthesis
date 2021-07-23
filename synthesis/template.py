from typing import TypeVar, Generic

from abc import ABC, abstractmethod

from synthesis import smt


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
