from dataclasses import dataclass
from typing import Iterator, cast

from zephyr_mbt_tool.tlaplus_values import TLAPlusInteger, TLAPlusModelValue, TLAPlusSequence, TLAPlusString
from zephyr_mbt_tool.tlc_counterexample import TLCCounterexample, TLCCounterexampleState, TLCCounterexampleTransition


@dataclass
class InterpretedCounterexampleState:
    state: TLCCounterexampleState

    @property
    def current_thread(self) -> int:
        if not isinstance(self.state["current"], TLAPlusInteger):
            raise ValueError("'current' must be an Integer")

        return self.state["current"].val

    @property
    def next_thread(self) -> int:
        if not isinstance(self.state["next"], TLAPlusInteger):
            raise ValueError("'next' must be an Integer")

        return self.state["next"].val

    @property
    def instructions(self) -> dict[int, list[str]]:
        """Return a dictionary mapping thread IDs to lists of instructions."""
        instructions = self.state["instructions"]
        if not isinstance(instructions, TLAPlusSequence):
            raise ValueError("'instructions' must be a sequence")

        ret = {}

        for tid, thread_instructions in instructions.items():
            if not all(
                isinstance(tla_str, TLAPlusString) for tla_str in cast(TLAPlusSequence, thread_instructions).values()
            ):
                raise ValueError("'instructions' must be a sequence of sequences of strings")
            ret[cast(TLAPlusInteger, tid).val] = list(
                cast(TLAPlusString, tla_str).val for tla_str in cast(TLAPlusSequence, thread_instructions).values()
            )

        return ret

    @property
    def shutdown_instructions(self) -> list[str] | None:
        shutdown_instructions = self.state["shutdown_instructions"]
        if shutdown_instructions == TLAPlusModelValue("NULL"):
            return None

        if not isinstance(shutdown_instructions, TLAPlusSequence) or not all(
            isinstance(tla_str, TLAPlusString) for tla_str in shutdown_instructions.values()
        ):
            raise ValueError("'shutdown_instructions' must be a sequence of strings")

        return list(cast(TLAPlusString, tla_str).val for tla_str in shutdown_instructions.values())

    @property
    def state_id(self) -> int:
        state_id = self.state["state_id"]
        if not isinstance(state_id, TLAPlusInteger):
            raise ValueError("'state_id' must be an integer")
        return state_id.val


@dataclass
class InterpretedTransition:
    _transition: TLCCounterexampleTransition

    @property
    def source_state(self) -> InterpretedCounterexampleState:
        return InterpretedCounterexampleState(self._transition.source_state)

    @property
    def dest_state(self) -> InterpretedCounterexampleState:
        return InterpretedCounterexampleState(self._transition.dest_state)

    @property
    def last_transition(self) -> bool:
        return self._transition.last_transition

    @property
    def in_loop(self) -> bool:
        return self._transition.in_loop


@dataclass
class InterpretedCounterexample:
    counterexample: TLCCounterexample

    @property
    def c_defines(self) -> list[str]:
        state1 = self.counterexample.state(1)
        c_defines = state1["defines"]
        if not isinstance(c_defines, TLAPlusSequence) or not all(
            isinstance(tla_val, TLAPlusString) for tla_val in c_defines.values()
        ):
            raise ValueError("Invalid counterexample: 'global_variables' in state1 must hold sequence of strings")

        return list(cast(TLAPlusString, tla_str_val).val for tla_str_val in c_defines.values())

    @property
    def global_variables(self) -> list[str]:
        state1 = self.counterexample.state(1)
        global_vars_seq = state1["global_variables"]
        if not isinstance(global_vars_seq, TLAPlusSequence) or not all(
            isinstance(tla_val, TLAPlusString) for tla_val in global_vars_seq.values()
        ):
            raise ValueError("Invalid counterexample: 'global_variables' in state1 must hold sequence of strings")

        return list(cast(TLAPlusString, tla_str_val).val for tla_str_val in global_vars_seq.values())

    @property
    def thread_ids(self) -> list[int]:
        state1 = self.counterexample.state(1)
        threads_seq = state1["threads"]
        if not isinstance(threads_seq, TLAPlusSequence):
            raise ValueError("Invalid counterexample: 'threads' in state1 must hold sequence")

        return list(cast(TLAPlusInteger, tla_int_val).val for tla_int_val in threads_seq.keys())

    @property
    def initialization_instructions(self) -> list[str]:
        state1 = self.counterexample.state(1)
        instructions = state1["initialization_instructions"]
        if not isinstance(instructions, TLAPlusSequence) or not all(
            isinstance(tlap_str, TLAPlusString) for tlap_str in instructions.values()
        ):
            raise ValueError(
                "Invalid counterexample: 'initialization_instructions' in state1 must hold sequence of strings"
            )

        return list(cast(TLAPlusString, tla_str_val).val for tla_str_val in instructions.values())

    def local_variables(self, thread_id: int) -> list[str]:
        state1 = self.counterexample.state(1)
        local_vars_seq = state1["local_variables"]
        if (
            not isinstance(local_vars_seq, TLAPlusSequence)
            or not all(isinstance(local_var_list, TLAPlusSequence) for local_var_list in local_vars_seq.values())
            or not all(
                isinstance(local_var_str, TLAPlusString)
                for local_var_str in cast(TLAPlusSequence, local_vars_seq[thread_id]).values()
            )
        ):
            raise ValueError(
                "Invalid counterexample: 'local_variables' in state1 must hold a sequence of sequences of strings"
            )

        return list(
            cast(TLAPlusString, tla_str_val).val
            for tla_str_val in cast(TLAPlusSequence, local_vars_seq[thread_id]).values()
        )

    def state(self, i: int) -> InterpretedCounterexampleState:
        """Return state i (1-indexed)"""
        return InterpretedCounterexampleState(self.counterexample.state(i))

    def transitions(self) -> Iterator[InterpretedTransition]:
        for trans in self.counterexample.transitions:
            yield InterpretedTransition(trans)
