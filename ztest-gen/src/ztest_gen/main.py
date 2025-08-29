import argparse
import os
import sys
from argparse import ArgumentParser
from typing import TextIO

from zephyr_mbt_tool.interpreted_counterexample import InterpretedCounterexample
from zephyr_mbt_tool.parse import CounterexampleParser
from zephyr_mbt_tool.zephyr_test_case import ZephyrTestCaseFactory
from zephyr_mbt_tool.zephyr_test_suite import ZephyrTestSuite


def parse_args() -> argparse.Namespace:
    parser = ArgumentParser()

    parser.add_argument(
        "input",
        type=str,
        help="The file containing the TLC output including one or more counterexamples. '-' for stdin",
    )

    parser.add_argument(
        "output",
        type=str,
        help="The C file to which the ZTest test suite should be written.",
    )

    parser.add_argument(
        "template_file",
        type=str,
        help="The Cog C file template.",
    )

    return parser.parse_args()


def build_test_suite(f: TextIO) -> ZephyrTestSuite:
    zephyr_test_suite = ZephyrTestSuite()

    for tlc_counterexample in CounterexampleParser().parse_counterexamples(f):
        interpreted_trace = InterpretedCounterexample(tlc_counterexample)
        factory = ZephyrTestCaseFactory(interpreted_trace)

        for transition in interpreted_trace.transitions():
            factory.add_transition(transition)

        zephyr_test_suite.test_cases.append(factory.test_case)

    return zephyr_test_suite


def process_input(f: TextIO, output: str | os.PathLike[str], template: str | os.PathLike[str]) -> None:
    test_suite = build_test_suite(f)
    test_suite.write_out(destination=output, cog_template=template)


def main() -> None:
    args = parse_args()

    if args.input == "-":
        process_input(sys.stdin, args.output, args.template_file)
    else:
        with open(args.input) as f:
            process_input(f, args.output, args.template_file)


if __name__ == "__main__":
    main()
