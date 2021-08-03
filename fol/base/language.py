"""
Many-sorted language
"""

from __future__ import annotations

from typing import Tuple, Optional, Iterable
from dataclasses import dataclass

from fol.smt import smt


class BaseAST: ...


@dataclass(frozen=True)
class Sort(BaseAST):
    name: str
    smt_hook: Optional[smt.SMTSort] = None

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class FunctionSymbol(BaseAST):
    input_sorts: Tuple[Sort, ...]
    output_sort: Sort
    name: str
    smt_hook: Optional[smt.SMTFunction] = None # if set, the function is interpreted as an SMT function

    def __str__(self) -> str:
        if len(self.input_sorts) == 0:
            return f"{self.name}: -> {self.output_sort}"

        input_sort_string = " ".join(map(str, self.input_sorts))
        return f"{self.name}: {input_sort_string} -> {self.output_sort}"


@dataclass(frozen=True)
class RelationSymbol(BaseAST):
    input_sorts: Tuple[Sort, ...]
    name: str
    smt_hook: Optional[smt.SMTFunction] = None # if set, the function is interpreted as an SMT function

    def __str__(self) -> str:
        if len(self.input_sorts) == 0:
            return f"{self.name}:"

        input_sort_string = " ".join(map(str, self.input_sorts))
        return f"{self.name}: {input_sort_string}"


@dataclass(frozen=True)
class Language:
    """
    A many-sorted language
    """
    sorts: Tuple[Sort, ...]
    function_symbols: Tuple[FunctionSymbol, ...]
    relation_symbols: Tuple[RelationSymbol, ...]

    def __str__(self) -> str:
        sort_string = ", ".join(map(str, self.sorts))
        function_symbol_string = ", ".join(map(str, self.function_symbols))
        relation_symbol_string = ", ".join(map(str, self.relation_symbols))
        return f"({sort_string}; {function_symbol_string}; {relation_symbol_string})"

    # TODO: add dict for sorts/functions/relations

    def get_sublanguage(
        self,
        sort_names: Iterable[str],
        function_names: Iterable[str],
        relation_names: Iterable[str],
    ) -> Language:
        sort_name_set = set(sort_names)
        function_name_set = set(function_names)
        relation_name_set = set(relation_names)
        return Language(
            tuple(sort for sort in self.sorts if sort.name in sort_name_set),
            tuple(function_symbol for function_symbol in self.function_symbols if function_symbol.name in function_name_set),
            tuple(relation_symbol for relation_symbol in self.relation_symbols if relation_symbol.name in relation_name_set),
        )

    def get_fresh_function_name(self, prefix: str) -> str:
        """
        Get a fresh function name in the form of <prefix><index>
        where index is the smallest integer such that
        <prefix><index> is not an existing function name
        """
        
        function_names = set(symbol.name for symbol in self.function_symbols)
        index = 0

        while True:
            name = f"{prefix}{index}"
            if name not in function_names:
                return name
            index += 1

        assert False

    def get_sort(self, name: str) -> Optional[Sort]:
        for sort in self.sorts:
            if sort.name == name:
                return sort
        return None

    def get_function_symbol(self, name: str) -> Optional[FunctionSymbol]:
        for symbol in self.function_symbols:
            if symbol.name == name:
                return symbol
        return None

    def get_relation_symbol(self, name: str) -> Optional[RelationSymbol]:
        for symbol in self.relation_symbols:
            if symbol.name == name:
                return symbol
        return None

    def get_max_function_arity(self) -> int:
        return max(tuple(len(symbol.input_sorts) for symbol in self.function_symbols) + (0,))

    def get_max_relation_arity(self) -> int:
        return max(tuple(len(symbol.input_sorts) for symbol in self.relation_symbols) + (0,))

    def expand(self, other: Language) -> Language:
        for sort in other.sorts:
            assert sort not in self.sorts, f"duplicate sort {sort}"

        for function_symbol in other.function_symbols:
            assert function_symbol not in self.function_symbols, f"duplicate function symbol {function_symbol}"

        for relation_symbol in other.relation_symbols:
            assert relation_symbol not in self.relation_symbols, f"duplicate relation symbol {relation_symbol}"

        return Language(
            self.sorts + other.sorts,
            self.function_symbols + other.function_symbols,
            self.relation_symbols + other.relation_symbols,
        )

    def expand_with_function(self, symbol: FunctionSymbol) -> Language:
        # TODO: check conflicts
        return Language(
            self.sorts,
            self.function_symbols + (symbol,),
            self.relation_symbols,
        )
