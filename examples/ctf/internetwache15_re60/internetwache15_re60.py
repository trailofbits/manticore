#!/usr/bin/env python3
"""
InternetWache CTF 2015 - RE60 FileChecker Challenge

This challenge involves a file checker that validates input.
The goal is to find the correct password/flag.

Expected flag: IW{FILE_CHeCKa}

Challenge Type: Binary Reverse Engineering
Platform: Linux x86_64
CTF: InternetWache CTF 2015
"""

import os
from manticore.native import Manticore


def solve_filechecker():
    """Solve the InternetWache FileChecker challenge."""
    
    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "filechecker")
    
    print("=" * 60)
    print("InternetWache CTF 2015 - RE60 FileChecker")
    print("=" * 60)
    
    # Create Manticore instance
    m = Manticore(binary_path)
    m.context["solved"] = False
    m.context["flag"] = []
    
    @m.hook(0x40067A)
    def skip_file_check(state):
        """Skip the actual file checking and jump to password check."""
        print("[*] Skipping file check")
        # Jump from file check to password validation
        state.cpu.PC = 0x4006CA
    
    @m.hook(0x4006E1)
    def skip_read_file(state):
        """Skip file reading operation."""
        print("[*] Skipping file read")
        # Jump over file reading
        state.cpu.PC = 0x400709
    
    @m.hook(0x400709)
    def inject_symbolic_password(state):
        """Inject symbolic values for password characters."""
        context = state.context
        flag = context.setdefault("flag", [])
        count = len(flag)
        
        # Create symbolic character
        char = state.new_symbolic_value(32, f"flag.{count}")
        
        # Constrain to printable ASCII
        state.constrain(char < 0x100)
        state.constrain(char > 0)
        
        # Write to stack location where fgetc result would be
        state.cpu.write_int(state.cpu.RBP - 0x18, char, 32)
        
        # Track the symbolic characters
        flag.append(char)
        
        print(f"[*] Injected symbolic character {count}")
    
    @m.hook(0x400732)
    def hook_failure(state):
        """Failure path - wrong password."""
        print("[-] Wrong password path - abandoning")
        state.abandon()
    
    @m.hook(0x400743)
    def hook_success(state):
        """Success path - correct password found!"""
        print("[+] Success! Found correct password")
        
        context = state.context
        flag_chars = []
        
        # Solve for each symbolic character
        for i, char_sym in enumerate(context.get("flag", [])):
            char_val = state.solve_one(char_sym)
            flag_chars.append(chr(char_val))
        
        flag = "".join(flag_chars)
        print(f"[+] FLAG: {flag}")
        
        # Check if it's the expected flag
        if flag == "IW{FILE_CHeCKa}":
            print("[+] Correct flag found!")
            with m.locked_context() as ctx:
                ctx["solved"] = True
                ctx["flag"] = flag
        
        m.kill()
    
    # Run symbolic execution
    print("\n[*] Starting symbolic execution...")
    m.run()
    
    # Check result
    if m.context.get("solved"):
        print(f"\n✅ Challenge solved!")
        print(f"Flag: {m.context.get('flag')}")
        return True
    else:
        print("\n⚠️  Flag not found")
        return False


if __name__ == "__main__":
    solve_filechecker()