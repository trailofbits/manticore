#!/usr/bin/env python3

import os

from manticore.native import Manticore

# Modified 'count_instructions.py' to demonstrate execution of a
# statically-linked "Hello, world!" AArch64 binary.

DIR = os.path.dirname(__file__)
FILE = os.path.join(DIR, "hello42")

if __name__ == "__main__":
    m = Manticore(FILE)

    with m.locked_context() as context:
        context["count"] = 0

    @m.hook(None)
    def explore(state):
        with m.locked_context() as context:
            context["count"] += 1

            if state.cpu.PC == 0x406F10:  # puts
                s = state.cpu.read_string(state.cpu.X0)
                assert s == "hello"
                print(f"puts argument: {s}")

            elif state.cpu.PC == 0x40706C:  # puts result
                result = state.cpu.X0
                assert result >= 0
                print(f"puts result: {result}")

            elif state.cpu.PC == 0x415E50:  # exit
                status = state.cpu.X0
                syscall = state.cpu.X8
                assert syscall == 94  # sys_exit_group
                print(f"exit status: {status}")

    def execute_instruction(self, insn, msg):
        print(f"{msg}: 0x{insn.address:x}: {insn.mnemonic} {insn.op_str}")

    m.subscribe(
        "will_execute_instruction",
        lambda self, state, pc, insn: execute_instruction(self, insn, "next"),
    )
    m.subscribe(
        "did_execute_instruction",
        lambda self, state, last_pc, pc, insn: execute_instruction(self, insn, "done"),
    )

    m.run()

    print(f"Executed {m.context['count']} instructions")
