from typing import Any, Iterator, TextIO
import json

from modelator_py.util.informal_trace_format import with_lists, with_records  # type: ignore
from modelator_py.util.tlc.stdout_to_informal_trace_format import (  # type: ignore
    extract_traces_from_file,
    tlc_trace_to_informal_trace_format_trace,
)

from zephyr_mbt_tool.tlc_counterexample import TLCCounterexample, TLCCounterexampleState

class InvalidCounterexampleException(Exception):
    pass


class CounterexampleParser:
    pass

class TLCJsonTraceParser(CounterexampleParser):

    def __init__(self, json_files: list[str]):
        self._json_files = json_files

    def _parse_dict(counterexample_dict: dict[str, Any]) -> TLCCounterexample:

        try:
            state_tuple_list = counterexample_dict["state"]
        except KeyError:
            raise InvalidCounterexampleException("")

        if not isinstance(state_tuple_list, list):
            raise InvalidCounterexampleException()

        try:
            state_tuple_list.sort(key=lambda item: item[0])
        except IndexError:
            raise InvalidCounterexampleException()

        state_list = [state_tuple[1] for state_tuple in state_tuple_list]

        tla_states = [
            TLCCounterexampleState.from_python_dict(state)
            for state in state_list
        ]

        return TLCCounterexample(tla_states, None)


    def parse_counterexamples(self, f: TextIO) -> Iterator[TLCCounterexample]:

        try:
            tlc_json_trace = json.load(f)

            yield self._parse_dict(tlc_json_trace)


        except json.JSONDecodeError:
            raise InvalidCounterexampleException("")




class TLCOutputParser(CounterexampleParser):

    def parse_counterexamples(f: TextIO) -> Iterator[TLCCounterexample]:
        for trace, loop_info in extract_traces_from_file(f):

            # first parse the states to get the ITF representation
            itf_trace = tlc_trace_to_informal_trace_format_trace(trace)
            itf_trace = with_records(with_lists(itf_trace))

            # from the itf representation, get our internal representation
            yield TLCCounterexample.from_itf_trace(itf_trace, loop_info)
