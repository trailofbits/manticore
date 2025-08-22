#!/usr/bin/env python3
"""
RPISEC Modern Binary Exploitation - Lab 1A

This lab requires finding a valid serial number for a given username.
The binary calculates a serial from the username and validates it.

Challenge Type: Serial Number Validation
Platform: Linux x86
Course: RPISEC MBE
"""

import os
from manticore.native import Manticore
from manticore.utils import log


def solve_lab1A():
    """Solve RPISEC MBE Lab 1A - find valid serial for username."""

    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "lab1A")

    print("=" * 60)
    print("RPISEC MBE - Lab 1A")
    print("=" * 60)

    # Initialize Manticore
    m = Manticore(binary_path)
    log.set_verbosity(1)  # verbosity method is deprecated

    @m.hook(0x8048B69)
    def inject_user_name(state):
        """Skip expensive I/O calls and inject username directly."""
        # Skip over expensive calls to puts/fgets/scanf
        state.cpu.RIP = 0x8048C1E

        # Because we're skipping the call to fgets/scanf, we'll have to inject our
        # data manually
        with m.locked_context() as context:
            user_name = "test123"
            serial_placeholder = 0xDEADBEEF  # arbitrary placeholder number

            # Inject variables
            username_address = state.cpu.ESP + 0x1C
            serial_address = state.cpu.ESP + 0x18
            context["username_address"] = username_address
            context["username"] = user_name

            print(f"[*] Injecting symbolic username: 0x{username_address:x}")
            print(f"[*] Injecting placeholder serial: 0x{serial_address:x}")

            state.cpu.write_bytes(username_address, user_name)
            state.cpu.write_int(serial_address, serial_placeholder)

    @m.hook(0x8048B31)
    def grab_serial(state):
        """
        This lab calculates a serial number from the provided username, and checks it
        against the provided serial number. By hooking the comparison, we can simply
        update our serial number in memory to match.
        """
        with m.locked_context() as context:
            print("[*] Recovering calculated serial")
            context["serial"] = state.cpu.read_int(state.cpu.EBP - 0x10)
            state.cpu.EAX = context["serial"]

    @m.hook(0x8048A23)
    def skip_strcspn(state):
        """
        strcspn is used to locate the newline character in our input. Because we're
        manually injecting our input, there will be no newline.
        """
        print("[*] Skipping call to strcspn")
        state.cpu.EIP = 0x8048A3E

    @m.hook(0x8048C36)
    def success(state):
        """
        If this address is reached, we know the username/serial number are valid.
        When this address is reached, dump the username and corresponding serial number.
        """
        with m.locked_context() as context:
            print("\n[+] Success path found!")
            print(f"[+] Username: {context['username']}")
            print(f"[+] Serial #: {context['serial']}")
            print("\n✅ Lab 1A solved!")
            m.terminate()

    # Run symbolic execution
    print("\n[*] Starting symbolic execution...")
    print("[*] Finding valid serial for username 'test123'")
    m.run()  # procs argument is no longer supported


if __name__ == "__main__":
    solve_lab1A()
