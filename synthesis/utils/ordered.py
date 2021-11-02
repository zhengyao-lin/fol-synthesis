from typing import Iterable, Generic, TypeVar, Dict, Iterator

from collections import OrderedDict


T = TypeVar("T")


class OrderedSet(Generic[T], Iterable[T]):
    def __init__(self, init: Iterable[T] = ()):
        self.collection: Dict[T, None] = OrderedDict()

        for elem in init:
            self.add(elem)

    def add(self, elem: T) -> None:
        self.collection[elem] = None

    def remove(self, elem: T) -> None:
        del self.collection[elem]

    def update(self, elems: Iterable[T]) -> None:
        for elem in elems:
            self.add(elem)

    def __contains__(self, elem: T) -> bool:
        return elem in self.collection

    def __iter__(self) -> Iterator[T]:
        return self.collection.keys().__iter__()

    def __repr__(self) -> str:
        return f"OrderedSet([{', '.join(map(repr, self))}])"

    def __str__(self) -> str:
        return repr(self)
