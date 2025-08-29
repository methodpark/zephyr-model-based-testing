import pytest

from ztest_gen.interpreted_counterexample import (
    InvalidCounterexampleException,
    InterpretedCEState,
)
from ztest_gen.tlaplus_values import TLAPlusFunction, TLAPlusSequence

THREAD1_INSTRUCTIONS = ["x++;", "g();"]
THREAD2_INSTRUCTIONS = ["assert(x, 1);"]
SHUTDOWN_INSTRUCTIONS = ["k_thread_abort(2);"]
VALID_RAW_STATE = {
    "state_id": 1,
    "current": 1,
    "next": 2,
    "instructions": TLAPlusFunction(
        (
            (1, TLAPlusSequence(THREAD1_INSTRUCTIONS)),
            (2, TLAPlusSequence(THREAD2_INSTRUCTIONS)),
        )
    ),
    "shutdown_instructions": TLAPlusSequence(SHUTDOWN_INSTRUCTIONS),
}


def test_parsed_counterexample_state_valid():
    raw_state = VALID_RAW_STATE

    parsed_ce = InterpretedCEState(raw_state)

    assert parsed_ce.state_id == 1
    assert parsed_ce.current_thread == 1
    assert parsed_ce.next_thread == 2
    assert parsed_ce.instructions_by_thread == {
        1: THREAD1_INSTRUCTIONS,
        2: THREAD2_INSTRUCTIONS,
    }
    assert parsed_ce.shutdown_instructions == SHUTDOWN_INSTRUCTIONS


def _copy_dict_without_key(d, key):
    return {k: v for k, v in d.items() if k != key}


def _copy_dict_replace_entry(d, key, new_val):
    ret = d.copy()
    ret[key] = new_val
    return ret


invalid_raw_states = [
    # missing variables
    _copy_dict_without_key(VALID_RAW_STATE, "state_id"),
    _copy_dict_without_key(VALID_RAW_STATE, "current"),
    _copy_dict_without_key(VALID_RAW_STATE, "next"),
    _copy_dict_without_key(VALID_RAW_STATE, "instructions"),
    _copy_dict_without_key(VALID_RAW_STATE, "shutdown_instructions"),
    # wrong types
    _copy_dict_replace_entry(VALID_RAW_STATE, "state_id", "1"),
    _copy_dict_replace_entry(VALID_RAW_STATE, "current", "1"),
    _copy_dict_replace_entry(VALID_RAW_STATE, "next", "1"),
    _copy_dict_replace_entry(VALID_RAW_STATE, "instructions", True),
    _copy_dict_replace_entry(  # string in instructions key
        VALID_RAW_STATE, "instructions", TLAPlusFunction((("1", TLAPlusSequence([])),))
    ),
    _copy_dict_replace_entry(  # value which is not a sequence
        VALID_RAW_STATE, "instructions", TLAPlusFunction(((1, False),))
    ),
    _copy_dict_replace_entry(  # value which is not a sequence
        VALID_RAW_STATE, "instructions", TLAPlusFunction(((1, False),))
    ),
    _copy_dict_replace_entry(  # value which is not a sequence of strings
        VALID_RAW_STATE,
        "instructions",
        TLAPlusFunction(((1, TLAPlusSequence([1, "x++"])),)),
    ),
    _copy_dict_replace_entry(VALID_RAW_STATE, "shutdown_instructions", True),
    _copy_dict_replace_entry(  # value which is not a sequence of strings
        VALID_RAW_STATE, "shutdown_instructions", TLAPlusSequence([1, "x++"])
    ),
]


@pytest.mark.parametrize("raw_state", invalid_raw_states, ids=lambda raw_s: repr(raw_s))
def test_parsed_counterexample_state_invalid(raw_state):
    with pytest.raises(InvalidCounterexampleException):
        InterpretedCEState(raw_state)
