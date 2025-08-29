from dataclasses import dataclass, field

from zephyr_mbt_tool.interpreted_counterexample import InterpretedCounterexample, InterpretedTransition


@dataclass
class ThreadFunction:
    local_variable_definitions: list[str] = field(default_factory=list)
    instructions: list[str] = field(default_factory=list)
    loop: list[str] | None = None

    def add_instructions(self, instructions: list[str], in_loop: bool) -> None:
        if in_loop:
            if self.loop is None:
                self.loop = []
            self.loop.extend(instructions)
        else:
            self.instructions.extend(instructions)


@dataclass
class ZephyrTestCase:
    main_thread_id: int
    global_variable_definitions: list[str] = field(default_factory=list)
    initialization_instructions: list[str] = field(default_factory=list)
    c_defines: list[str] = field(default_factory=list)
    thread_functions: dict[int, ThreadFunction] = field(default_factory=dict)

    @property
    def num_threads(self) -> int:
        return len(self.thread_functions)


class ZephyrTestCaseFactory:

    def __init__(self, trace: InterpretedCounterexample):
        self.test_case = ZephyrTestCase(
            main_thread_id=trace.state(1).current_thread,
            global_variable_definitions=trace.global_variables,
            c_defines=trace.c_defines,
            initialization_instructions=trace.initialization_instructions,
            thread_functions={
                tid: ThreadFunction(local_variable_definitions=trace.local_variables(tid)) for tid in trace.thread_ids
            },
        )

    def add_transition(self, transition: InterpretedTransition) -> None:
        src_state = transition.source_state
        dest_state = transition.dest_state
        in_loop = transition.in_loop

        next_thread = src_state.next_thread
        next_thread_function = self.test_case.thread_functions[next_thread]

        for tid, instruction_list in src_state.instructions.items():
            self.test_case.thread_functions[tid].add_instructions(instruction_list, in_loop)

        if transition.last_transition and dest_state.shutdown_instructions:  # TODO: consider loop case
            next_thread_function.add_instructions(dest_state.shutdown_instructions, False)
