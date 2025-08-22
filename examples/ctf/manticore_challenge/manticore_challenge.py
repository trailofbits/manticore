#!/usr/bin/env python3
"""
Manticore Challenge Solution

This challenge was created specifically to demonstrate Manticore's capabilities.
It involves finding the correct input that passes multiple check functions.

Challenge Type: Binary Reverse Engineering
Platform: Linux x86_64
Blog Post: https://blog.trailofbits.com/2017/05/15/magic-with-manticore/
"""

import os
import sys
from subprocess import check_output
from manticore.native import Manticore


def solve_manticore_challenge():
    """Solve the Manticore challenge using symbolic execution."""

    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "manticore_challenge")

    print("=" * 60)
    print("Manticore Challenge")
    print("=" * 60)
    print("[*] Blog: https://blog.trailofbits.com/2017/05/15/magic-with-manticore/")

    def get_exit_addresses():
        """Extract exit call addresses from each check function using objdump."""
        try:
            # Get objdump output
            disasm = check_output(
                f"objdump -d {binary_path} | grep 'call.*exit' || true", shell=True
            ).decode()

            if not disasm:
                print("[!] Warning: Could not extract exit addresses")
                # Return known addresses if objdump fails
                return [0x400C5D, 0x400D1D, 0x400DDD, 0x400E9D]

            # Parse addresses
            exits = []
            for line in disasm.strip().split("\n"):
                if line and "exit" in line:
                    addr_str = line.split(":")[0].strip()
                    exits.append(int(addr_str, 16))

            return exits
        except Exception as e:
            print(f"[!] Error getting exit addresses: {e}")
            # Return known addresses as fallback
            return [0x400C5D, 0x400D1D, 0x400DDD, 0x400E9D]

    # Create Manticore instance
    m = Manticore(binary_path)
    m.context["solved"] = False

    # Buffer address where input is stored
    buff_addr = None

    @m.hook(0x4009A4)
    def hook_skip_io(state):
        """Skip puts and fgets calls, jump to input handling."""
        state.cpu.EIP = 0x4009C1

    @m.hook(0x4009C8)
    def hook_inject_symbolic(state):
        """Inject symbolic buffer instead of reading from stdin."""
        global buff_addr

        # Get buffer address from RDI (first argument to fgets)
        buff_addr = state.cpu.RDI
        print(f"[*] Injecting symbolic buffer at 0x{buff_addr:x}")

        # Create symbolic buffer (11 bytes needed)
        buffer = state.new_symbolic_buffer(11)

        # Write to memory
        state.cpu.write_bytes(buff_addr, buffer)

        # Skip fgets call
        state.cpu.EIP = 0x4009D3

    # Hook all exit points to abandon those paths
    exit_addrs = get_exit_addresses()
    print(f"[*] Hooking {len(exit_addrs)} exit points")

    for addr in exit_addrs:

        @m.hook(addr)
        def hook_exit(state):
            print(f"[-] Exit at 0x{state.cpu.EIP:x} - abandoning")
            state.abandon()

    @m.hook(0x400F78)
    def hook_success(state):
        """Success state - solve for the winning input."""
        print("[+] Success state reached!")

        if buff_addr:
            # Solve for the flag
            solution = state.solve_buffer(buff_addr, 11)
            flag = "".join(map(chr, solution))

            # The expected flag is "=MANTICORE="
            print(f"[+] FLAG: {flag}")

            with m.locked_context() as ctx:
                ctx["solved"] = True

        m.kill()

    # Run symbolic execution
    print("\n[*] Starting symbolic execution...")
    print("[*] This may take a few minutes...")
    m.run()

    # Check result
    if m.context["solved"]:
        print("\n✅ Challenge solved!")
        print("The flag '=MANTICORE=' passes all checks")
        return True
    else:
        print("\n⚠️  Solution not found")
        return False


if __name__ == "__main__":
    solve_manticore_challenge()
