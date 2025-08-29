from __future__ import annotations

from abc import ABC
from collections.abc import Iterator, Mapping, Set
from dataclasses import dataclass, field
from typing import Any, Iterable, Sequence, cast


@dataclass(frozen=True)
class TLAPlusValue(ABC):

    @classmethod
    def from_python_value(cls, pyval: bool | int | str | dict | list) -> TLAPlusValue:
        match pyval:
            case bool():
                return TLAPlusBoolean(pyval)
            case int():
                return TLAPlusInteger(pyval)
            case str():
                return TLAPlusString(pyval)
            case dict():
                mapping = {
                    cls.from_python_value(k): cls.from_python_value(v)
                    for k, v in pyval.items()
                }
                return TLAPlusRecord(mapping)
            case list():
                seq = [cls.from_python_value(v) for v in pyval]
                return TLAPlusSequence(seq)

        raise ValueError(f"Python Value cannot be converted to TLAPlus value {pyval}")


@dataclass(frozen=True)
class TLAPlusInteger(TLAPlusValue):
    _val: int

    def __int__(self) -> int:
        return self._val


@dataclass(frozen=True)
class TLAPlusBoolean(TLAPlusValue):
    _val: bool

    def __bool__(self) -> bool:
        return self._val


@dataclass(frozen=True)
class TLAPlusString(TLAPlusValue):
    _val: str

    def __str__(self) -> str:
        return self._val


@dataclass(frozen=True)
class TLAPlusModelValue(TLAPlusValue):
    identifier: str


@dataclass(frozen=True)
class TLAPlusFunction(TLAPlusValue, Mapping[TLAPlusValue | str | int, TLAPlusValue]):
    """
    Represents a TLA+ function as an immutable mapping from keys to values.
    """

    _mapping: tuple[tuple[TLAPlusValue, TLAPlusValue]]

    def __init__(self, mapping: Iterable[tuple[TLAPlusValue, TLAPlusValue]]) -> None:
        object.__setattr__(self, "_mapping", tuple(mapping))  # can't set mapping normally because of frozen property

    def __len__(self) -> int:
        """Returns the number of key-value pairs in the function."""
        return len(self._mapping)

    def __eq__(self, other: Any) -> bool:
        """Checks equality with another TLAPlusFunction based on their mappings."""
        return isinstance(other, TLAPlusFunction) and set(self._mapping) == set(other._mapping)

    def __iter__(self) -> Iterator[TLAPlusValue]:
        """Iterates over the keys of the function."""
        return iter(m[0] for m in self._mapping)

    def __getitem__(self, item: TLAPlusValue | str | int) -> TLAPlusValue:
        """
        Retrieves the value associated with the given key.
        Pythonic str and int are accepted for convenience and are treated like the corresponding TLAPlus values.
        Raises ValueError if the key is not present in the function.
        """

        # Convert item to a TLAPlusValue, if necessary
        k: TLAPlusValue = (
            item
            if isinstance(item, TLAPlusValue)
            else TLAPlusString(item) if isinstance(item, str) else TLAPlusInteger(item)
        )

        for m in self._mapping:
            if m[0] == k:
                return m[1]

        raise ValueError(f"Key {item} not present in domain of function {self}")


@dataclass(frozen=True)
class TLAPlusSequence(TLAPlusFunction):
    """
    A TLA+ Sequence is a TLA+ Function, whose domain are natural numbers 1..n.
    """

    def __init__(self, values: Sequence[TLAPlusValue]) -> None:
        super().__init__(iter(TLAPlusInteger(i), val) for i, val in enumerate(values, 1))

    def __iter__(self) -> Iterator[TLAPlusInteger]:
        return cast(Iterator[TLAPlusInteger], super().__iter__())

    def __getitem__(self, item: TLAPlusValue | int | str) -> TLAPlusValue:
        if not (isinstance(item, int) or isinstance(item, TLAPlusInteger)):
            raise ValueError(f"Sequence lookup with invalid key: {item}")

        return self._mapping[int(item) - 1]


@dataclass(frozen=True)
class TLAPlusRecord(TLAPlusFunction, Mapping[TLAPlusString | str, TLAPlusValue]):

    def __init__(self, dictionary: Mapping[str, TLAPlusValue]) -> None:
        super().__init__(tuple((TLAPlusString(k), val) for k, val in dictionary.items()))

    def __iter__(self) -> Iterator[TLAPlusString]:
        return cast(Iterator[TLAPlusString], super().__iter__())


@dataclass(frozen=True)
class TLAPlusSet(TLAPlusValue, Set[TLAPlusValue]):
    _set: frozenset[TLAPlusValue] = field()

    def __init__(self, set: Iterable[TLAPlusValue]) -> None:
        object.__setattr__(self, "_set", frozenset(set))  # can't set set normally because of frozen property

    def __contains__(self, x: Any) -> bool:
        return x in self._set

    def __len__(self) -> int:
        return len(self._set)

    def __iter__(self) -> Iterator[TLAPlusValue]:
        return iter(self._set)
