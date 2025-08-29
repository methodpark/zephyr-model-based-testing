import pytest
from ztest_gen.tlaplus_values import TLAPlusFunction, TLAPlusInteger, TLAPlusString, TLAPlusModelValue, TLAPlusBoolean

def test_primitive_types():

    int_0 = TLAPlusInteger(0)
    int_1 = TLAPlusInteger(1)
    str_a = TLAPlusString("a")
    mv_null = TLAPlusModelValue("NULL")
    bool_false = TLAPlusBoolean(False)

    assert(int_0 == TLAPlusInteger(0))
    assert(int_0 != int_1)
    assert(int(int_0) == 0)

    assert(str_a != int_0)
    assert(str_a != TLAPlusString(""))
    assert(str_a == TLAPlusString("a"))
    assert(str(str_a) == "a")

    assert(mv_null != str_a)
    assert(mv_null != int_0)
    assert(mv_null != TLAPlusModelValue("null"))
    assert(mv_null == TLAPlusModelValue("NULL"))

    assert(bool(bool_false) is False)
    assert(bool_false != str_a)
    assert(bool_false != int_0)
    assert(bool_false != mv_null)
    assert(bool_false != TLAPlusBoolean(True))
    assert(bool_false == TLAPlusBoolean(False))

def test_tlaplus_function():

    f_id = TLAPlusFunction(
        [
            (TLAPlusInteger(1), TLAPlusInteger(1))
        ]
    )

    assert(TLAPlusInteger(1) in f_id)
    assert(f_id[TLAPlusInteger(1)] == TLAPlusInteger(1))
    assert(f_id[1] == TLAPlusInteger(1))
    assert(list(iter(f_id)) == [TLAPlusInteger(1)])
