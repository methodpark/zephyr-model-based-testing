from ztest_gen.tlc_counterexample import TLCCounterexample, TLCCounterexampleTransition


def test_counterexample_finite_2_states():
    state1 = {"a": 1, "b": 2}
    state2 = {"a": 2, "b": 2}

    states = [state1, state2]

    tlc_ce = TLCCounterexample(states, None)

    assert tlc_ce.lasso_shaped is False
    assert len(tlc_ce) == len(states)
    assert tlc_ce.first_state == state1
    assert tlc_ce.last_state == state2
    assert tlc_ce.first_loop_state is None

    assert list(tlc_ce.states) == states
    assert tlc_ce.state(1) == state1
    assert tlc_ce.state(2) == state2

    transitions = list(tlc_ce.transitions())
    assert len(transitions) == 1
    assert transitions[0].source_state == state1
    assert transitions[0].dest_state == state2
    assert transitions[0].in_loop is False
    assert transitions[0].last_transition is True


def test_counterexample_finite_3_states():
    state1 = {"a": 1, "b": 2}
    state2 = {"a": 2, "b": 2}
    state3 = {"a": 3, "b": 2}

    states = [state1, state2, state3]

    tlc_ce = TLCCounterexample(states, None)

    assert tlc_ce.lasso_shaped is False
    assert len(tlc_ce) == len(states)
    assert tlc_ce.first_state == state1
    assert tlc_ce.last_state == state3
    assert tlc_ce.first_loop_state is None
    assert list(tlc_ce.states) == states

    transitions = list(tlc_ce.transitions())
    assert len(transitions) == 2
    assert transitions[0].source_state == state1
    assert transitions[0].dest_state == state2
    assert transitions[0].in_loop is False
    assert transitions[0].last_transition is False

    assert transitions[1].source_state == state2
    assert transitions[1].dest_state == state3
    assert transitions[1].in_loop is False
    assert transitions[1].last_transition is True


def test_counterexample_lasso():
    state1 = {"a": 1, "b": 2}
    state2 = {"a": 2, "b": 2}
    state3 = {"a": 3, "b": 2}

    states = [state1, state2, state3]

    tlc_ce = TLCCounterexample(states, 2)

    assert tlc_ce.lasso_shaped is True
    assert tlc_ce.first_loop_state == state2
    assert tlc_ce.last_state == state3

    assert list(tlc_ce.states) == states
    assert list(tlc_ce.transitions()) == [
        TLCCounterexampleTransition(
            state1, state2, in_loop=False, last_transition=False
        ),
        TLCCounterexampleTransition(
            state2, state3, in_loop=True, last_transition=False
        ),
        TLCCounterexampleTransition(state3, state2, in_loop=True, last_transition=True),
    ]
