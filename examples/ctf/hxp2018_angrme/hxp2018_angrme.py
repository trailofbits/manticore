#!/usr/bin/env python3
"""
HXP CTF 2018 - angrme Challenge

This challenge requires finding the correct flag that passes validation.
The binary uses position-independent code (PIE).

Expected flag: hxp{4nd_n0w_f0r_s0m3_r3al_ch4ll3ng3}

Challenge Type: Binary Reverse Engineering
Platform: Linux x86_64 (PIE enabled)
CTF: HXP CTF 2018
"""

import os
from manticore.native import Manticore
from manticore.core.smtlib import operators
from manticore.utils import log


def solve_angrme():
    """Solve the HXP angrme challenge using symbolic execution."""

    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "angrme")

    print("=" * 60)
    print("HXP CTF 2018 - angrme")
    print("=" * 60)

    # Create Manticore instance
    m = Manticore(binary_path)
    m.context["solved"] = False
    m.context["input_address"] = None

    # Maximum flag length estimate
    max_length = 40

    # Note: These addresses assume ASLR is disabled or we're using base addresses
    # In real scenario, you might need to calculate offsets from binary base

    @m.hook(0x555555555187)
    def inject_symbolic_input(state):
        """Skip fgets and inject symbolic input directly."""
        print("[*] Injecting symbolic input")

        # Skip expensive fgets call
        state.cpu.RIP = 0x5555555551A0

        # Create symbolic buffer
        solution = state.new_symbolic_buffer(max_length)

        # Constrain flag format - must start with "hxp{"
        state.constrain(solution[0] == ord("h"))
        state.constrain(solution[1] == ord("x"))
        state.constrain(solution[2] == ord("p"))
        state.constrain(solution[3] == ord("{"))

        # Constrain characters to printable ASCII or null
        for i in range(max_length):
            state.constrain(
                operators.OR(
                    solution[i] == 0,  # null terminator
                    operators.AND(ord(" ") <= solution[i], solution[i] <= ord("}")),
                )
            )

        # Calculate input address and write symbolic buffer
        address = state.cpu.RSP + 0x30
        print(f"[*] Input address: 0x{address:x}")

        # Save address in context
        with m.locked_context() as context:
            context["input_address"] = address

        # Write symbolic buffer to memory
        state.cpu.write_bytes(address, solution)

    @m.hook(0x555555556390)
    def hook_failure(state):
        """Abandon paths that reach the failure function."""
        print("[-] Failure path - abandoning")
        state.abandon()

    @m.hook(0x555555556370)
    def hook_success(state):
        """Success path - solve for the flag."""
        print("[+] Success path found!")

        with m.locked_context() as context:
            address = context["input_address"]

        if address:
            # Solve for the flag
            flag_bytes = state.solve_buffer(address, max_length)
            flag = "".join(map(chr, flag_bytes)).rstrip("\x00")

            print(f"[+] FLAG: {flag}")

            # Check if it's the expected flag
            if "hxp{4nd_n0w_f0r_s0m3_r3al_ch4ll3ng3}" in flag:
                print("[+] Correct flag found!")
                with m.locked_context() as context:
                    context["solved"] = True

        m.kill()

    # Set verbosity for debugging
    log.set_verbosity(1)  # verbosity method is deprecated

    # Run symbolic execution
    print("\n[*] Starting symbolic execution...")
    print("[*] Note: This binary uses PIE, addresses may need adjustment")
    m.run()

    # Check result
    if m.context["solved"]:
        print("\n✅ Challenge solved!")
        return True
    else:
        print("\n⚠️  Flag not found")
        print("    This might be due to PIE/ASLR - addresses may need adjustment")
        return False


if __name__ == "__main__":
    solve_angrme()
