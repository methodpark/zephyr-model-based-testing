from dataclasses import dataclass
from typing import Iterator, Sequence, cast
from ztest_gen.tlaplus_values import TLAPlusFunction, TLAPlusSequence
from ztest_gen.tlc_counterexample import (
    TLCCounterexample,
    TLCCounterexampleState,
    TLCCounterexampleTransition,
)


class InvalidCounterexampleException(Exception):
    pass


@dataclass
class InterpretedCEState:
    raw_state: TLCCounterexampleState

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        """Access each property to detect invalid states."""
        self.current_thread
        self.next_thread
        self.state_id
        self.instructions_by_thread
        self.shutdown_instructions

    def _variable_present_with_type(self, var: str, t: type) -> bool:
        return var in self.raw_state and isinstance(self.raw_state[var], t)

    def _raise_if_variable_invalid(self, var: str, t: type) -> None:
        if not self._variable_present_with_type(var, t):
            raise InvalidCounterexampleException(
                f"State does not contain a '{var}' or value is not of type {t}: {self.raw_state}"
            )

    @property
    def state_id(self) -> int:
        """The 1-indexed index of this state in the counterexample."""
        self._raise_if_variable_invalid("state_id", int)
        return cast(int, self.raw_state["state_id"])

    @property
    def current_thread(self) -> int:
        """The thread expected to be running in this state."""
        self._raise_if_variable_invalid("current", int)
        return cast(int, self.raw_state["current"])

    @property
    def next_thread(self) -> int:
        """The thread expected to be running in the next state."""
        self._raise_if_variable_invalid("next", int)
        return cast(int, self.raw_state["next"])

    @property
    def instructions_by_thread(self) -> dict[int, list[str]]:
        """
        A dictionary mapping thread ids to lists of instructions that should be appended
        to the thread's C function for the transition starting in this state.
        """
        self._raise_if_variable_invalid("instructions", TLAPlusFunction)

        function = cast(TLAPlusFunction, self.raw_state["instructions"])

        ret = {}

        for thread_id, instruction_sequence in function.items():
            # Check wether the function has only thread IDs (integers) in its domain.
            if not isinstance(thread_id, int):
                raise InvalidCounterexampleException(
                    "The 'instructions' function has keys that are not valid thread IDs (integers)."
                )

            # Check wether the function has only sequences of strings as values.
            if not isinstance(instruction_sequence, TLAPlusSequence) or not all(
                isinstance(instr, str) for instr in instruction_sequence.values()
            ):
                raise InvalidCounterexampleException(
                    "The 'instructions' function has values that are not sequences of strings."
                )

            instruction_list = list(instruction_sequence.values())
            ret[thread_id] = cast(list[str], instruction_list)

        return ret

    @property
    def shutdown_instructions(self) -> list[str]:
        self._raise_if_variable_invalid("shutdown_instructions", TLAPlusSequence)

        instruction_seq = cast(TLAPlusSequence, self.raw_state["shutdown_instructions"])

        # Check wether all sequence values are strings
        if not all(isinstance(instr, str) for instr in instruction_seq.values()):
            raise InvalidCounterexampleException(
                "The 'shutdown_instructions' sequence holds values that are not strings."
            )

        instruction_list = list(instruction_seq.values())
        return cast(list[str], instruction_list)


@dataclass
class InterpretedCETransition:
    _transition: TLCCounterexampleTransition

    @property
    def source_state(self) -> InterpretedCEState:
        return InterpretedCEState(self._transition.source_state)

    @property
    def dest_state(self) -> InterpretedCEState:
        return InterpretedCEState(self._transition.dest_state)

    @property
    def last_transition(self) -> bool:
        return self._transition.last_transition

    @property
    def in_loop(self) -> bool:
        return self._transition.in_loop


@dataclass
class InterpretedCounterexample:
    raw_counterexample: TLCCounterexample

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        self.defines
        self.global_variables
        self.initialization_instructions
        for tid in self.thread_ids:
            self.local_variables(tid)
        self.states

    def _get_str_list_from_initial_state(self, var_name: str) -> list[str]:
        seq = self.raw_counterexample.first_state.get(var_name)
        if (
            seq is None
            or not isinstance(seq, TLAPlusSequence)
            or not all(isinstance(val, str) for val in seq.values())
        ):
            raise InvalidCounterexampleException(
                f"First state does not contain a '{var_name}' variable that holds a sequence of strings"
            )

        ret = list(seq.values())
        return cast(list[str], ret)

    @property
    def defines(self) -> list[str]:
        return self._get_str_list_from_initial_state("defines")

    @property
    def global_variables(self) -> list[str]:
        return self._get_str_list_from_initial_state("global_variables")

    @property
    def initialization_instructions(self) -> list[str]:
        return self._get_str_list_from_initial_state("initialization_instructions")

    @property
    def thread_ids(self) -> set[int]:
        thread_func = self.raw_counterexample.first_state.get("threads")
        if (
            thread_func is None
            or not isinstance(thread_func, TLAPlusFunction)
            or not all(isinstance(k, int) for k in thread_func)
        ):
            raise InvalidCounterexampleException(
                "The first state does not contain a 'threads' variable that holds a function of integers."
            )

        ret = set(thread_func.keys())
        return cast(set[int], ret)

    def local_variables(self, thread_id: int) -> list[str]:
        local_var_func = self.raw_counterexample.first_state.get("local_variables")
        if (
            local_var_func is None
            or not isinstance(local_var_func, TLAPlusFunction)
            or thread_id not in local_var_func
        ):
            raise InvalidCounterexampleException(
                f"The first state does not contain a 'local_variables' variable with '{thread_id}' in its domain."
            )

        local_var_seq = local_var_func[thread_id]

        if not isinstance(local_var_seq, TLAPlusSequence) or not all(
            isinstance(val, str) for val in local_var_seq.values()
        ):
            raise InvalidCounterexampleException(
                f"The 'local_variables' entry for thread '{thread_id}' is not a sequence of strings."
            )

        ret = list(local_var_seq.values())
        return cast(list[str], ret)

    def state(self, i: int) -> InterpretedCEState:
        return InterpretedCEState(self.raw_counterexample.state(i))

    @property
    def states(self) -> Sequence[InterpretedCEState]:
        return [
            InterpretedCEState(raw_state)
            for raw_state in self.raw_counterexample.states
        ]

    def transitions(self) -> Iterator[InterpretedCETransition]:
        for transition in self.raw_counterexample.transitions():
            yield InterpretedCETransition(transition)
