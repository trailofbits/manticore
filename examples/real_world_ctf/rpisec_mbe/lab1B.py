#!/usr/bin/env python3
"""
RPISEC Modern Binary Exploitation - Lab 1B

This lab has a switch statement with 21 cases. We need to find which
case leads to success by systematically testing each one.

Challenge Type: Control Flow Analysis
Platform: Linux x86
Course: RPISEC MBE
"""

import os
from manticore.native import Manticore


def solve_lab1B():
    """Solve RPISEC MBE Lab 1B - find correct password case."""
    
    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "lab1B")
    
    print("=" * 60)
    print("RPISEC MBE - Lab 1B")
    print("=" * 60)
    
    # Initialize Manticore
    m = Manticore(binary_path)
    m.verbosity(1)
    
    # This lab has 21 unique cases equivalent to:
    # switch(0x1337d00d - input):
    #     case(1):
    #         ...
    #     case(2):
    #         ...
    #     ...
    #     case(21):
    #         ...
    #
    # By setting our input to 0x1337d00d - 1, we ensure we will hit the first case
    m.context["password"] = 0x1337D00D - 1
    
    @m.hook(0x8048A55)
    def bad_password(state):
        """
        If this address is reached, the password check has failed. Luckily, there
        are a limited number of possible cases. We can decrement our input to reach
        the next case, then manually jump back to the switch.
        """
        with m.locked_context() as context:
            print("[-] Invalid password - trying next case")
            
            context["password"] -= 1
            state.cpu.EIP = 0x8048BF6
    
    @m.hook(0x8048A4E)
    def success(state):
        """
        If this code is reached, our password must have been correct. Dump our input
        when this address is reached.
        """
        with m.locked_context() as context:
            print("\n[+] Success path found!")
            print(f"[+] Password: 0x{context['password']:x}")
            print(f"[+] Decimal: {context['password']}")
            print("\n✅ Lab 1B solved!")
            m.terminate()
    
    @m.hook(0x8048BF6)
    def inject_data(state):
        """
        Instead of sending input through stdin, it's more efficient to jump
        over calls to I/O functions like fgets or puts and inject our data
        manually onto the stack. Because these libc functions are so massive, this
        can give us significant performance improvements.
        """
        with m.locked_context() as context:
            # Skip ahead several instructions to jump over puts/fgets/scanf
            state.cpu.EIP = 0x8048C52
            
            print(f"[*] Injecting password: 0x{context['password']:x}")
            state.cpu.EAX = context["password"]
    
    # Run symbolic execution
    print("\n[*] Starting symbolic execution...")
    print("[*] Testing switch cases to find correct password")
    m.run(procs=10)


if __name__ == "__main__":
    solve_lab1B()