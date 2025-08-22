#!/usr/bin/env python3
"""
AIS3 Crackme Challenge Solution

This CTF challenge requires finding a valid input that passes the binary's checks.
The expected flag is: ais3{I_tak3_g00d_n0t3s}

Challenge Type: Binary Reverse Engineering
Platform: Linux x86_64
"""

import os
from manticore.native import Manticore


def solve_ais3_crackme():
    """Solve the AIS3 crackme challenge using symbolic execution."""

    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "ais3_crackme")

    print("=" * 60)
    print("AIS3 Crackme Challenge")
    print("=" * 60)

    # Create Manticore instance with initial argument
    m = Manticore(binary_path, ["a" * 30])

    buffer_addr = 0
    num_bytes = 24

    # Track success in context
    with m.locked_context() as w:
        w["found_flag"] = False
        w["buffer_addr"] = 0

    @m.hook(0x4005CD)
    def hook_fake_args(state):
        """Fake 2 arguments by setting EDI=2"""
        print("[*] Faking 2 arguments: EDI=2")
        state.cpu.EDI = 0x2

    @m.hook(0x4005F3)
    def hook_get_buffer(state):
        """Retrieve buffer from RAX and inject symbolic data"""
        print("[*] Retrieving buffer from RAX")

        # Create symbolic buffer with constraints for known prefix
        solution = state.new_symbolic_buffer(num_bytes)

        # Add constraints for known flag format
        state.constrain(solution[0] == ord("a"))
        state.constrain(solution[1] == ord("i"))
        state.constrain(solution[2] == ord("s"))
        state.constrain(solution[3] == ord("3"))
        state.constrain(solution[4] == ord("{"))

        # Get buffer address and store symbolic data
        buffer_addr = state.cpu.read_int(state.cpu.RAX)
        state.cpu.write_bytes(buffer_addr, solution)

        # Save buffer address in context
        with m.locked_context() as w:
            w["buffer_addr"] = buffer_addr

        print(f"[*] Buffer address: 0x{buffer_addr:08x}")

    @m.hook(0x40060E)
    def hook_failure(state):
        """Abandon paths that reach failure"""
        print("[-] Failure path reached, abandoning")
        state.abandon()

    @m.hook(0x400602)
    def hook_success(state):
        """Success path - solve for the flag"""
        print("[+] Success path reached! Attempting to solve...")

        with m.locked_context() as w:
            buffer_addr = w["buffer_addr"]

        if buffer_addr:
            # Solve for the flag
            res = "".join(map(chr, state.solve_buffer(buffer_addr, num_bytes)))
            print(f"[+] FLAG: {res}")

            # Check if it's the expected flag
            if res == "ais3{I_tak3_g00d_n0t3s}":
                print("[+] Correct flag found!")
                with m.locked_context() as w:
                    w["found_flag"] = True

        m.kill()

    # Run symbolic execution
    m.verbosity = 1
    print("\n[*] Starting symbolic execution...")
    m.run()

    # Check result
    with m.locked_context() as w:
        if w["found_flag"]:
            print("\n✅ Challenge solved!")
            return True
        else:
            print("\n⚠️  Flag not found (may need more time or different approach)")
            return False


if __name__ == "__main__":
    solve_ais3_crackme()
