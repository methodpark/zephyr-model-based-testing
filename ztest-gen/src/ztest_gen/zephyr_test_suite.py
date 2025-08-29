import os
from dataclasses import dataclass, field

from cogapp import Cog  # type: ignore

from zephyr_mbt_tool.zephyr_test_case import ZephyrTestCase


@dataclass
class ZephyrTestSuite:
    test_cases: list[ZephyrTestCase] = field(default_factory=list)

    @property
    def global_variable_definitions(self) -> set[str]:
        """The global variables of a test suite is the union of the global variables of all test cases."""
        global_variables = set()
        for test_case in self.test_cases:
            global_variables.update(test_case.global_variable_definitions)
        return global_variables

    @property
    def c_defines(self) -> set[str]:
        """The global variables of a test suite is the union of the global variables of all test cases."""
        c_defines = set()
        for test_case in self.test_cases:
            c_defines.update(test_case.c_defines)
        return c_defines

    def write_out(self, destination: str | os.PathLike[str], cog_template: str | os.PathLike[str]) -> None:
        cog_global_vars = {
            "global_var_defs": self.global_variable_definitions,
            "c_defines": self.c_defines,
            "INDENT": "    ",
            "test_cases": self.test_cases,
        }

        cog = Cog()
        cog.options.bDeleteCode = True
        cog.processFile(str(cog_template), str(destination), globals=cog_global_vars)
