#!/usr/bin/env python3
"""
BugsBunny CTF 2017 - Rev 150

This challenge requires finding a 20-digit password through partial analysis
and incremental search. The solution uses hooks to inject and test passwords.

Expected solution: 42813724579039578812

Challenge Type: Password Cracking via Hook-based Injection
Platform: Linux x86_64
CTF: BugsBunny CTF 2017

NOTE: The rev150 binary is not included in this repository.
      You need to obtain the original challenge binary to run this example.
      The file 'rev150' in this directory is a placeholder HTML file.

      See issue #2675 for details: https://github.com/trailofbits/manticore/issues/2675
"""

import os
import sys
from manticore.native import Manticore
from manticore.utils import log


def solve_rev150():
    """
    Solve the BugsBunny CTF 2017 Rev 150 challenge.

    The challenge requires finding a 20-digit numeric password.
    From IDA Pro analysis, we can deduce most of the digits.
    The script incrementally searches for the correct value.
    """

    # Get binary path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "rev150")

    print("=" * 60)
    print("BugsBunny CTF 2017 - Rev 150")
    print("=" * 60)

    # Parse command line arguments
    if len(sys.argv) > 1:
        prog = sys.argv[1]
        params = sys.argv[2:] if len(sys.argv) > 2 else ["00000000000000000000"]
    else:
        # Use the actual binary if it exists
        if os.path.exists(os.path.join(script_dir, "rev150_binary")):
            prog = os.path.join(script_dir, "rev150_binary")
        else:
            prog = binary_path
        params = ["00000000000000000000"]  # Initial dummy password

    print(f"[*] Binary: {prog}")
    print(f"[*] Initial params: {params}")

    # Check if binary exists and is valid
    if not os.path.exists(prog):
        print(f"\n❌ Error: Binary '{prog}' not found!")
        print("Please download the actual rev150 binary from the CTF.")
        return

    # Check if it's actually a binary (not HTML)
    with open(prog, "rb") as f:
        header = f.read(4)
        if header[:4] != b"\x7fELF":
            print(f"\n❌ Error: '{prog}' is not a valid ELF binary!")
            print("The file appears to be HTML or text. Please download the actual binary.")
            print("\nNote: The rev150 file in this directory is a placeholder.")
            print("You need to download the actual challenge binary.")
            return

    # Initialize Manticore
    m = Manticore(prog, params)

    # Set initial password based on partial analysis
    # We know most digits from IDA Pro analysis
    with m.locked_context() as context:
        context["password"] = 42810720579039578812  # Starting point
        context["found"] = False

    @m.hook(0x401BE2)
    def inject_password(state):
        """
        At this point, we inject our chosen password into the address
        holding the password inputted to the binary.
        The password is formatted to be 20 digits long.
        """
        with m.locked_context() as context:
            formatted_pwd = f"{context['password']:020}"
            print(f"[*] Injecting password: {formatted_pwd}")
            state.cpu.write_bytes(state.cpu.RDI, formatted_pwd)

    @m.hook(0x401E5A)
    def failed(state):
        """
        If the password is incorrect, we will increment the password
        (so long as it remains 20 digits) and return to the original
        point of injection.
        """
        with m.locked_context() as context:
            if len(str(context["password"])) == 20:
                context["password"] += 1000000000000  # Increment specific digits
                state.cpu.RIP = 0x401BE2  # Jump back to injection point
                print("[-] Incorrect password, trying next...")
            else:
                print("[-] No password found within search space")
                m.terminate()

    @m.hook(0x401E49)
    def success(state):
        """
        If our password passes all of the checks, we can return it as the flag.
        """
        with m.locked_context() as context:
            print("\n[+] Success!")
            print(f"[+] Password: {context['password']}")
            print(f"[+] Flag: BugsBunny{{{context['password']}}}")  # Double {{ for literal {, then expression
            context["found"] = True
            m.terminate()

    # Set verbosity and run
    log.set_verbosity(1)  # verbosity method is deprecated

    print("\n[*] Starting symbolic execution...")
    print("[*] This may take several minutes (~9 minutes expected)")
    print("[*] Searching for 20-digit password...")

    m.run()

    # Check result
    with m.locked_context() as context:
        if context["found"]:
            print("\n✅ Challenge solved!")
            return True
        else:
            print("\n⚠️  Challenge not solved")
            return False


if __name__ == "__main__":
    solve_rev150()
