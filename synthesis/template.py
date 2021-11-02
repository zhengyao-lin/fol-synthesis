from typing import TypeVar, Generic, Iterable, Tuple

from abc import ABC, abstractmethod

from .smt import smt


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


# class BoundedIntegerVariable(Template[int]):
#     """
#     An integer variable with range lower upper
#     """

#     def __init__(self, lower: int, upper: int):
#         assert upper >= lower
#         self.lower = lower
#         self.upper = upper
#         self.num_bits = (upper - lower + 1).bit_length()
#         self.variable = smt.FreshSymbol(typename=smt.BVType(self.num_bits))

#     def get_constraint(self) -> smt.SMTTerm:
#         raise NotImplementedError()
#         # return smt.TRUE()

#     def get_from_smt_model(self, model: smt.SMTModel) -> int:
#         return model[self.variable].bv2nat() + self.lower # type: ignore

#     def equals(self, value: int) -> smt.SMTTerm:
#         return smt.Equals(self.variable, smt.BV(value - self.lower, self.num_bits))

#     def get_range(self) -> Iterable[int]:
#         return range(self.lower, self.upper + 1)


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


class UnionTemplate(Template[T]):
    def __init__(self, *templates: Template[T]):
        assert len(templates) != 0
        self.node = BoundedIntegerVariable(0, len(templates))
        self.templates = tuple(templates)

    def get_constraint(self) -> smt.SMTTerm:
        return smt.Or(*(
            smt.And(
                self.node.equals(node_value),
                template.get_constraint(),
            )
            for node_value, template in enumerate(self.templates, 1)
        ))

    def get_from_smt_model(self, model: smt.SMTModel) -> T:
        node_value = self.node.get_from_smt_model(model)
        assert 1 <= node_value <= len(self.templates), \
               f"invalid node value {node_value}"
        return self.templates[node_value - 1].get_from_smt_model(model)

    def equals(self, value: T) -> smt.SMTTerm:
        return smt.Or(*(
            smt.And(self.node.equals(node_value), template.equals(value))
            for node_value, template in enumerate(self.templates, 1))
        )
