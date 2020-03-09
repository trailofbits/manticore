#!/usr/bin/env python

import sys

from manticore import issymbolic
from manticore.native import Manticore

"""
Replaces a variable that controls program flow with a tainted symbolic value. This
in turn explores all possible states under that variable's influence, and reports the
specific cmp/test instructions can be influenced by tainted data.

Usage:

 $ gcc -static -g src/state_explore.c -o state_explore # -static is optional
 $ ADDRESS=0x$(objdump -S state_explore | grep -A 1 '((value & 0xff) != 0)' |
         tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
 $ python ./introduce_symbolic_bytes.py state_explore $ADDRESS
 Tainted Control Flow:
 introducing symbolic value to 7ffffffffd44
 400a0e: test eax, eax
 400a19: cmp eax, 0x3f
 400b17: test eax, eax
 400b1e: cmp eax, 0x1000
 400b63: test eax, eax
 400a3e: cmp eax, 0x41
 400a64: cmp eax, 0x42
 400a8a: cmp eax, 0x43
 400ab0: cmp eax, 0x44
 400b6a: cmp eax, 0xf0000
 Analysis finished. See ./mcore_cz3Jzp for results.
"""

if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.stderr.write(f"Usage: {sys.argv[0]} [binary] [address]\n")
        sys.exit(2)

    # Passing a parameter to state_explore binary disables reading the value
    # from STDIN, and relies on us adding it manually
    m = Manticore(sys.argv[1], ["anything"])

    # Uncomment to see debug output
    # m.verbosity = 2

    # Set to the address of the instruction before the first conditional.
    introduce_at = int(sys.argv[2], 0)

    taint_id = "taint_A"

    @m.hook(introduce_at)
    def introduce_sym(state):
        # RBP-0xC is the location of the value we're interested in:
        #
        #    if ((value & 0xff) != 0) {
        #  400a08:       8b 45 f4                mov    -0xc(%rbp),%eax
        #  400a0b:       0f b6 c0                movzbl %al,%eax
        #  400a0e:       85 c0                   test   %eax,%eax
        #

        print(f"introducing symbolic value to {state.cpu.RBP-0xc:x}")

        val = state.new_symbolic_value(32, taint=(taint_id,))
        state.cpu.write_int(state.cpu.RBP - 0xC, val, 32)

    def has_tainted_operands(operands, taint_id):
        # type: (list[manticore.core.cpu.abstractcpu.Operand], object) -> bool
        for operand in operands:
            op = operand.read()
            if issymbolic(op) and taint_id in op.taint:
                return True
        return False

    every_instruction = None

    @m.hook(every_instruction)
    def check_taint(state):
        insn = state.cpu.instruction  # type: capstone.CsInsn
        if insn is None:
            return
        if insn.mnemonic in ("cmp", "test"):
            if has_tainted_operands(insn.operands, taint_id):
                print(f"{insn.address:x}: {insn.mnemonic} {insn.op_str}")

    print("Tainted Control Flow:")
    m.run()

    print(f"Analysis finished. See {m.workspace} for results.")
