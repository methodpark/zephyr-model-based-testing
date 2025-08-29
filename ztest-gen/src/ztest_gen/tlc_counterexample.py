from __future__ import annotations

from dataclasses import dataclass
from itertools import pairwise
from typing import Iterator, Mapping, Sequence

from modelator_py.util.informal_trace_format import ITFState, ITFTrace  # type: ignore

from zephyr_mbt_tool.tlaplus_values import TLAPlusValue


@dataclass(frozen=True)
class TLCCounterexampleState(Mapping[str, TLAPlusValue]):
    var_mapping: Mapping[str, TLAPlusValue]

    def __getitem__(self, key: str, /) -> TLAPlusValue:
        """Retrieve the value of the variable named key."""
        return self.var_mapping[key]

    def __len__(self) -> int:
        """The number of variables in the state."""
        return len(self.var_mapping)

    def __iter__(self) -> Iterator[str]:
        return iter(self.var_mapping)

    @classmethod
    def from_itf_state(cls, itf_state: ITFState) -> TLCCounterexampleState:
        return cls({var_name: TLAPlusValue.from_itf_value(val) for var_name, val in itf_state.var_value_map.items()})

    @classmethod
    def from_python_dict(cls, state_dict: dict[str: int | str | dict | list]) -> TLCCounterexampleState:
        return cls(
            {
                var_name: TLAPlusValue.from_python_value(val)
                for var_name, val in state_dict.items()
            }
        )


@dataclass
class TLCCounterexampleTransition:
    source_state: TLCCounterexampleState
    dest_state: TLCCounterexampleState
    in_loop: bool
    last_transition: bool


@dataclass(frozen=True)
class TLCCounterexample:
    _state: Sequence[TLCCounterexampleState]
    _loop_start: int | None  # the (1-indexed) first state of the loop in case of lasso. Else None.

    @property
    def lasso_shaped(self) -> bool:
        return self._loop_start is not None

    def __len__(self) -> int:
        """The number of states in the counterexample."""
        return len(self._state)

    def state(self, i: int) -> TLCCounterexampleState:
        """Return state i (1-indexed!)."""
        return self._state[i - 1]

    @property
    def states(self) -> Sequence[TLCCounterexampleState]:
        return self._state

    @property
    def first_state(self) -> TLCCounterexampleState:
        return self._state[0]

    @property
    def last_state(self) -> TLCCounterexampleState:
        """The last state. In case of a lasso, this is the last state in the loop before
        returning to the first state in the loop.
        """
        return self._state[-1]

    @property
    def first_loop_state(self) -> TLCCounterexampleState | None:
        """None for a regular counterexample. The first state in the loop in case of a lasso."""
        return None if self._loop_start is None else self.state(self._loop_start)

    @property
    def transitions(self) -> Iterator[TLCCounterexampleTransition]:
        for i, (s1, s2) in enumerate(pairwise(self._state), 1):
            in_loop = self._loop_start is not None and self._loop_start <= i
            last_transition = s1 is self._state[-2] and not in_loop
            yield TLCCounterexampleTransition(s1, s2, in_loop, last_transition)

        # In case of a lasso, there is one last transition from the last state of the state sequence
        # back to the first state in the loop.
        if self.first_loop_state is not None:
            yield TLCCounterexampleTransition(self.last_state, self.first_loop_state, True, last_transition=True)

    @classmethod
    def from_itf_trace(cls, itf_trace: ITFTrace, loop_info: None | tuple[int, int]) -> TLCCounterexample:
        trace = [TLCCounterexampleState.from_itf_state(itf_state) for itf_state in itf_trace.states]

        return cls(trace, loop_info[0] if loop_info else None)
