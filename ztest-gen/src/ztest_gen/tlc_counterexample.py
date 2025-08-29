from __future__ import annotations

from dataclasses import dataclass
from itertools import pairwise
from typing import Iterator, Sequence, TypeAlias

from ztest_gen.tlaplus_values import TLAPlusValue

TLCCounterexampleState: TypeAlias = dict[str, TLAPlusValue]


@dataclass
class TLCCounterexampleTransition:
    source_state: TLCCounterexampleState
    dest_state: TLCCounterexampleState
    in_loop: bool
    last_transition: bool


@dataclass(frozen=True)
class TLCCounterexample:
    _state: Sequence[TLCCounterexampleState]

    # the (1-indexed) first state of the loop in case of lasso. Else None.
    _loop_start: int | None

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
        """
        The last state. In case of a lasso, this is the last state in the loop before
        returning to the first state in the loop.
        """
        return self._state[-1]

    @property
    def first_loop_state(self) -> TLCCounterexampleState | None:
        """None for a regular counterexample. The first state in the loop in case of a lasso."""
        return None if self._loop_start is None else self.state(self._loop_start)

    def transitions(self) -> Iterator[TLCCounterexampleTransition]:
        for i, (s1, s2) in enumerate(pairwise(self._state), 1):
            # If counterexample is lasso-shaped and s1 is the loop start or a later state,
            # the transition is in the loop.
            in_loop = self._loop_start is not None and self._loop_start <= i

            # If this is a regular counterexample and s1 is the 2nd last state,
            # this is the last transtion.
            last_transition = s1 is self._state[-2] and not in_loop

            yield TLCCounterexampleTransition(s1, s2, in_loop, last_transition)

        # In case of a lasso, there is one last transition from the last state of the state sequence
        # back to the first state in the loop.
        if self.first_loop_state is not None:
            yield TLCCounterexampleTransition(
                self.last_state, self.first_loop_state, True, last_transition=True
            )
