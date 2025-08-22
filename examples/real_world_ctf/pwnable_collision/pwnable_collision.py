#!/usr/bin/env python3
"""
Pwnable.kr - Collision Challenge

This challenge requires finding an input that causes a hash collision.
The program takes a 20-byte input and needs it to hash to a specific value.

Challenge Type: Hash Collision via Symbolic Execution
Platform: Linux x86_64
Source: pwnable.kr
"""

import os
from manticore.native import Manticore
from manticore.core.smtlib import operators


def solve_collision():
    """
    Solve the collision challenge using symbolic execution.
    
    The challenge requires finding a 20-byte input where the sum of 
    5 integers (4 bytes each) equals a specific target value.
    """
    
    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "col")
    
    print("=" * 60)
    print("Pwnable.kr - Collision Challenge")
    print("=" * 60)
    
    # Initialize Manticore with symbolic argv[1] (20 bytes)
    m = Manticore(binary_path, ["+" * 20])
    m.context["solution"] = None
    m.context["argv1"] = None
    
    @m.init
    def init_handler(initial_state):
        """Define constraints for symbolic ARGV before execution."""
        print("[*] Setting up symbolic argv[1]")
        
        # Find the symbolic argv[1] from input symbols
        argv1 = None
        for sym in initial_state.input_symbols:
            if sym.name == "ARGV1":
                argv1 = sym
                break
        
        if argv1 is None:
            raise Exception("ARGV was not made symbolic")
        
        # Constrain to printable ASCII characters
        print("[*] Applying ASCII constraints")
        for i in range(20):
            initial_state.constrain(
                operators.AND(
                    ord(" ") <= argv1[i],
                    argv1[i] <= ord("}")
                )
            )
        
        # Store argv1 reference in context
        with m.locked_context() as context:
            context["argv1"] = argv1
    
    # Hook failure paths to abandon them
    @m.hook(0x400C2F)
    def fail_wrong_length(state):
        """Wrong input length."""
        print("[-] Wrong length - abandoning")
        state.abandon()
    
    @m.hook(0x400BE7)
    def fail_wrong_hash(state):
        """Wrong hash value."""
        print("[-] Wrong hash - abandoning")
        state.abandon()
    
    @m.hook(0x400BAC)
    def fail_check(state):
        """Failed check."""
        print("[-] Failed check - abandoning")
        state.abandon()
    
    @m.hook(0x400BA6)
    def skip_syscalls(state):
        """Skip error-checking syscalls to speed up execution."""
        print("[*] Skipping syscalls")
        state.cpu.EIP = 0x400BFA
    
    @m.hook(0x400C1C)
    def success_state(state):
        """Success! Found collision input."""
        print("[+] Success state reached!")
        
        with m.locked_context() as context:
            argv1 = context["argv1"]
            if argv1:
                # Solve for the concrete input value
                solution = state.solve_one(argv1, 20)
                context["solution"] = solution
                
                # Print solution in different formats
                if solution:
                    print(f"[+] Found collision input!")
                    print(f"    Raw bytes: {solution}")
                    print(f"    Hex: {solution.hex()}")
                    
                    # Try to print as string if possible
                    try:
                        solution_str = solution.decode('ascii', errors='replace')
                        print(f"    ASCII: {solution_str}")
                    except:
                        pass
        
        m.kill()
    
    # Run symbolic execution
    print("\n[*] Starting symbolic execution...")
    print("[*] Looking for 20-byte input that causes hash collision...")
    m.verbosity(2)
    m.run()
    
    # Check result
    solution = m.context.get("solution")
    if solution:
        print("\n✅ Challenge solved!")
        print(f"Collision input: {solution}")
        
        # Explain the collision
        print("\n[*] Explanation:")
        print("    The program interprets the 20 bytes as 5 integers")
        print("    and sums them. The collision occurs when this sum")
        print("    equals the target value (0x21DD09EC).")
        
        return True
    else:
        print("\n⚠️  No solution found")
        return False


if __name__ == "__main__":
    solve_collision()