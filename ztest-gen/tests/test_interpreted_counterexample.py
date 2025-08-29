import pytest
from ztest_gen.interpreted_counterexample import (
    InvalidCounterexampleException,
    InterpretedCounterexample,
)
from ztest_gen.tlaplus_values import python_value_to_tlaplus
from ztest_gen.tlc_counterexample import TLCCounterexample

VALID_FIRST_STATE = {
    "defines": python_value_to_tlaplus(["#define X 1"]),
    "global_variables": python_value_to_tlaplus(["int y;"]),
    "local_variables": python_value_to_tlaplus({1: ["int ret;"], 2: ["int ret2;"]}),
    "initialization_instructions": python_value_to_tlaplus(["f();"]),
    "threads": python_value_to_tlaplus({1: "", 2: ""}),
    "current": 1,
    "next": 1,
    "state_id": 1,
    "instructions": python_value_to_tlaplus({1: ["f();"], 2: ["g();"]}),
    "shutdown_instructions": python_value_to_tlaplus(["exit1();"]),
}

VALID_SECOND_STATE = {
    "current": 1,
    "next": 2,
    "state_id": 2,
    "instructions": python_value_to_tlaplus({1: ["h();"], 2: ["m();"]}),
    "shutdown_instructions": python_value_to_tlaplus(["exit2();"]),
}

VALID_RAW_COUNTEREXAMPLE = TLCCounterexample(
    [VALID_FIRST_STATE, VALID_SECOND_STATE],
    None,
)


def test_parsed_counterexample_valid():
    parsed_ce = InterpretedCounterexample(VALID_RAW_COUNTEREXAMPLE)

    assert parsed_ce.defines == ["#define X 1"]
    assert parsed_ce.global_variables == ["int y;"]
    assert parsed_ce.local_variables(1) == ["int ret;"]
    assert parsed_ce.local_variables(2) == ["int ret2;"]
    assert parsed_ce.initialization_instructions == ["f();"]
    assert parsed_ce.thread_ids == {1, 2}

    assert parsed_ce.state(1).current_thread == 1
    assert parsed_ce.state(1).next_thread == 1
    assert parsed_ce.state(1).state_id == 1
    assert parsed_ce.state(1).instructions_by_thread == {1: ["f();"], 2: ["g();"]}
    assert parsed_ce.state(1).shutdown_instructions == ["exit1();"]

    assert parsed_ce.state(2).current_thread == 1
    assert parsed_ce.state(2).next_thread == 2
    assert parsed_ce.state(2).state_id == 2
    assert parsed_ce.state(2).instructions_by_thread == {1: ["h();"], 2: ["m();"]}
    assert parsed_ce.state(2).shutdown_instructions == ["exit2();"]


def _copy_dict_without_key(d, key):
    return {k: v for k, v in d.items() if k != key}


def _copy_dict_replace_entry(d, key, new_val):
    ret = d.copy()
    ret[key] = new_val
    return ret


invalid_first_states_missing_variable = [
    # missing variables in first state
    TLCCounterexample(
        [_copy_dict_without_key(VALID_FIRST_STATE, k), VALID_SECOND_STATE],
        None,
    )
    for k in [
        "defines",
        "global_variables",
        "local_variables",
        "initialization_instructions",
        "threads",
        "shutdown_instructions",
        "current",
        "next",
        "state_id",
        "instructions",
    ]
]

invalid_first_states_missing_wrong_type = [
    TLCCounterexample(
        [
            _copy_dict_replace_entry(
                VALID_FIRST_STATE, var_name, python_value_to_tlaplus(pyval)
            ),
            VALID_SECOND_STATE,
        ],
        None,
    )
    for (var_name, pyval) in [
        ("defines", {"1": "1"}),  # record instead of string sequence
        ("defines", [1, 2]),  # int sequence instead of string sequence
        ("global_variables", {"1": "1"}),
        ("global_variables", [1, 2]),
        ("initialization_instructions", {"1": "1"}),
        ("initialization_instructions", [1, 2]),
        ("threads", {"1": "1"}),  # record instead of function from int
        ("local_variables", {"1": "1"}),  # record instead of function from int
    ]
]

invalid_second_states = [
    TLCCounterexample(
        [VALID_FIRST_STATE, _copy_dict_without_key(VALID_SECOND_STATE, k)],
        None,
    )
    for k in [
        "shutdown_instructions",
        "current",
        "next",
        "state_id",
        "instructions",
    ]
]

invalid_raw_ces = (
    invalid_first_states_missing_variable
    + invalid_first_states_missing_wrong_type
    + invalid_second_states
)


@pytest.mark.parametrize("raw_ce", invalid_raw_ces, ids=lambda raw_s: repr(raw_s))
def test_parsed_counterexample_invalid(raw_ce):
    with pytest.raises(InvalidCounterexampleException):
        InterpretedCounterexample(raw_ce)
