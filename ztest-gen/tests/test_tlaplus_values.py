import pytest

from ztest_gen.tlaplus_values import (
    TLAPlusFunction,
    TLAPlusRecord,
    TLAPlusSequence,
    TLAPlusSet,
    python_value_to_tlaplus,
)

testdata = [
    (1, 1),
    ("1", "1"),
    (True, True),
    (
        {1: 1, 2: 2, "3": "3"},
        TLAPlusFunction(((1, 1), (2, 2), ("3", "3"))),
    ),
    (
        {"1": 1, "2": 2, "3": 3},
        TLAPlusRecord({"1": 1, "2": 2, "3": 3}),
    ),
    (
        [1, "2", 3],
        TLAPlusSequence([1, "2", 3]),
    ),
    (
        {1, 2, 3},
        TLAPlusSet([1, 2, 3]),
    ),
]


def idfn(py_val) -> str:
    return repr(py_val)


@pytest.mark.parametrize("py_val,tlaplus_val", testdata, ids=idfn)
def test_tlaplus_value_python_value_to_tlaplus(py_val, tlaplus_val):
    assert python_value_to_tlaplus(py_val) == tlaplus_val


def test_tlaplus_function_simple():
    f_id = python_value_to_tlaplus({1: 1})

    assert isinstance(f_id, TLAPlusFunction)
    assert 1 in f_id
    assert 2 not in f_id
    assert f_id[1] == 1
    assert list(f_id) == [1]
    assert len(f_id) == 1


def test_tlaplus_function_mixed_keys():
    f = python_value_to_tlaplus({1: 1, "2": 2})

    assert 1 in f
    assert f[1] == 1

    assert "2" in f
    assert f["2"] == 2

    assert len(f) == 2


def test_tlaplus_functions_equality():
    f1 = TLAPlusFunction(
        (
            (1, 1),
            (2, 2),
        )
    )
    f2 = TLAPlusFunction(
        (
            (2, 2),
            (1, 1),
        )
    )
    f3 = python_value_to_tlaplus({1: 1, "2": "2"})

    # f1 and f2 must be equal despite different key order
    assert f1 == f2
    assert list(f1) == [1, 2]
    assert list(f2) == [2, 1]

    assert f1 != f3
    assert f2 != f3


def test_tlaplus_record():
    record = python_value_to_tlaplus({"a": 1, "b": 2})
    f = TLAPlusFunction(
        (
            ("a", 1),
            ("b", 2),
        )
    )

    assert isinstance(record, TLAPlusRecord)
    assert isinstance(record, TLAPlusFunction)

    assert record == f


def test_tlaplus_sequence():
    seq = python_value_to_tlaplus([True, False, True])
    f = TLAPlusFunction(
        (
            (3, True),
            (2, False),
            (1, True),
        )
    )

    assert isinstance(seq, TLAPlusSequence)
    assert isinstance(seq, TLAPlusFunction)

    assert seq == f
    assert list(seq) == [1, 2, 3]


def test_tlaplus_set():
    s1 = python_value_to_tlaplus({1, 2})
    s2 = TLAPlusSet([1, 1, 2])

    assert isinstance(s1, TLAPlusSet)
    assert s1 == s2
    assert len(s1) == 2
    assert 1 in s1
    assert 3 not in s1


def test_compound_function_keys():
    tlaplus_set = python_value_to_tlaplus({1, 2})
    tlaplus_seq = python_value_to_tlaplus([1, 2])
    tlaplus_rec = python_value_to_tlaplus({"1": 1, "2": 2})
    tlaplus_func = python_value_to_tlaplus({"1": 1, 2: 2})

    assert isinstance(tlaplus_set, TLAPlusSet)
    assert isinstance(tlaplus_seq, TLAPlusSequence)
    assert isinstance(tlaplus_rec, TLAPlusRecord)
    assert isinstance(tlaplus_func, TLAPlusFunction)

    f = TLAPlusFunction(
        (
            (tlaplus_set, 1),
            (tlaplus_seq, 2),
            (tlaplus_rec, 3),
            (tlaplus_func, 4),
        )
    )

    assert f[tlaplus_set] == 1
    assert f[tlaplus_seq] == 2
    assert f[tlaplus_rec] == 3
    assert f[tlaplus_func] == 4
