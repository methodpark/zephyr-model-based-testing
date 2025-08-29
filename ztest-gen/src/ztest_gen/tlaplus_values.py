from __future__ import annotations

from collections.abc import Iterator, Mapping, Set
from dataclasses import dataclass, field
from typing import Any, Iterable, Sequence, cast, TypeAlias


def python_value_to_tlaplus(
    pyval: bool | int | str | dict | list | set,
) -> TLAPlusValue:
    """
    Converts a Python value into its corresponding TLA+ value representation.
    Supported Python types and their TLA+ equivalents:
    - bool, int, str: Returned as-is.
    - dict: Converted to a TLAPlusRecord if all keys are strings, otherwise to a TLAPlusFunction.
    - list, tuple: Converted to a TLAPlusSequence.
    - set, frozenset: Converted to a TLAPlusSet.
    Args:
        pyval (bool | int | str | dict | list | set): The Python value to convert.
    Returns:
        TLAPlusValue: The TLA+ representation of the input value.
    Raises:
        ValueError: If the input value cannot be converted to a TLA+ value.
    """
    match pyval:
        case bool() | int() | str():
            return pyval

        case dict():
            mapping = {
                python_value_to_tlaplus(k): python_value_to_tlaplus(v)
                for k, v in pyval.items()
            }

            if all(isinstance(k, str) for k in mapping):
                return TLAPlusRecord(cast(dict[str, TLAPlusValue], mapping))
            else:
                return TLAPlusFunction(tuple(mapping.items()))

        case list() | tuple():
            seq = [python_value_to_tlaplus(v) for v in pyval]
            return TLAPlusSequence(seq)

        case set() | frozenset():
            return TLAPlusSet(pyval)

    raise ValueError(f"Python Value cannot be converted to TLAPlus value {pyval}")


@dataclass(frozen=True)
class TLAPlusFunction(Mapping["TLAPlusValue", "TLAPlusValue"]):
    """
    Represents a TLA+ function as an immutable mapping from keys to values.
    """

    # Can't use a dict because TLAPlusFunction must be hashable
    _mapping: tuple[tuple[TLAPlusValue, TLAPlusValue], ...]

    def __len__(self) -> int:
        """Returns the number of key-value pairs in the function."""
        return len(self._mapping)

    def __eq__(self, other: Any) -> bool:
        """Checks equality with another TLAPlusFunction based on their mappings."""
        return isinstance(other, TLAPlusFunction) and set(self._mapping) == set(
            other._mapping
        )

    def __iter__(self) -> Iterator[TLAPlusValue]:
        """Iterates over the keys of the function in the order in which the keys were passed to __init__."""
        return iter(m[0] for m in self._mapping)

    def __getitem__(self, item: TLAPlusValue) -> TLAPlusValue:
        """
        Retrieves the value associated with the given key.
        Raises KeyError if the key is not present in the function.
        """

        for key, val in self._mapping:
            if key == item:
                return val

        raise KeyError(f"Key {item} not present in domain of function {self}")


@dataclass(frozen=True)
class TLAPlusSequence(TLAPlusFunction, Mapping[int, "TLAPlusValue"]):
    """
    A TLA+ Sequence is a TLA+ Function, whose domain is the set of natural numbers {1..n}.
    """

    def __init__(self, values: Sequence[TLAPlusValue]) -> None:
        super().__init__(tuple(enumerate(values, 1)))

    def __iter__(self) -> Iterator[int]:
        """Iterate over the indices 1..n in ascending order."""
        return cast(Iterator[int], super().__iter__())

    def __getitem__(self, item: TLAPlusValue) -> TLAPlusValue:
        if not isinstance(item, int):
            raise KeyError(f"Sequence lookup with invalid key: {item}")

        # Position of key in _mapping tuple is known.
        return self._mapping[item - 1][1]


@dataclass(frozen=True)
class TLAPlusRecord(TLAPlusFunction, Mapping[str, "TLAPlusValue"]):
    """
    A TLA+ Record is a TLA+ Function, whose domain is a set of strings.
    """

    def __init__(self, dictionary: Mapping[str, TLAPlusValue]) -> None:
        super().__init__(tuple(dictionary.items()))

    def __iter__(self) -> Iterator[str]:
        return cast(Iterator[str], super().__iter__())


@dataclass(frozen=True)
class TLAPlusSet(Set["TLAPlusValue"]):
    _set: frozenset[TLAPlusValue] = field()

    def __init__(self, set: Iterable[TLAPlusValue]) -> None:
        object.__setattr__(
            self, "_set", frozenset(set)
        )  # can't set set normally because of frozen property

    def __contains__(self, x: Any) -> bool:
        return x in self._set

    def __len__(self) -> int:
        return len(self._set)

    def __iter__(self) -> Iterator[TLAPlusValue]:
        return iter(self._set)


TLAPlusValue: TypeAlias = bool | int | str | TLAPlusFunction | TLAPlusSet
