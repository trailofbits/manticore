#!/usr/bin/env python3
"""
Google CTF 2016: Unbreakable Enterprise Product Activation Challenge

This is a solution to the Google CTF 2016 reverse engineering challenge
"unbreakable-enterprise-product-activation" using Manticore.

Challenge Description:
- Binary performs a complex check on user input
- Goal: Find the activation key that passes all checks
- The flag format is CTF{...}

Original Author: @ctfhacker
Challenge Link: https://github.com/ctfs/write-ups-2016/tree/master/google-ctf-2016/reverse/unbreakable-enterprise-product-activation-150

This example demonstrates:
- Binary analysis with symbolic execution
- Constraint-based input generation
- Hooking to control execution flow
- Finding valid inputs without reverse engineering the algorithm
"""

import os
import sys
from manticore.native import Manticore


def solve_unbreakable():
    """
    Solve the Google CTF 2016 Unbreakable challenge using symbolic execution.

    Returns:
        str: The flag that passes all checks
    """
    print("=" * 70)
    print("Google CTF 2016: Unbreakable Enterprise Product Activation")
    print("=" * 70)

    # Load the binary
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "unbreakable")

    if not os.path.exists(binary_path):
        print(f"❌ Binary not found: {binary_path}")
        print("Note: This example requires the Linux x86_64 binary")
        return None

    print(f"\nLoading binary: {binary_path}")

    # Check if we're on a compatible platform
    import platform

    if platform.system() != "Linux" or platform.machine() not in ["x86_64", "AMD64"]:
        print("⚠️  Warning: This binary is for Linux x86_64.")
        print("   It may not work correctly on your platform.")
        print(f"   Current platform: {platform.system()} {platform.machine()}")

    # Create Manticore instance
    m = Manticore(binary_path)

    # Track if we found the solution
    m.context["solved"] = False
    m.context["flag"] = None

    # These addresses are specific to the binary
    # Found through static analysis at 0x4005b8
    INPUT_ADDR = 0x6042C0  # Global buffer where input is stored
    INPUT_SIZE = 0x33  # Size of the input buffer

    print("\nSetting up hooks...")

    @m.hook(0x400729)  # Entry point hook
    def hook_entry(state):
        """
        Hook at the entry point to inject symbolic input.
        We skip the actual input reading and jump directly to the check.
        """
        print("  [*] Entry point reached - injecting symbolic input")

        # Create a symbolic buffer for our input
        # The buffer is slightly larger than needed (0x43 vs 0x33)
        buffer = state.new_symbolic_buffer(0x43)

        # Apply known constraints: the flag starts with "CTF{"
        # This helps reduce the search space significantly
        state.constrain(buffer[0] == ord("C"))
        state.constrain(buffer[1] == ord("T"))
        state.constrain(buffer[2] == ord("F"))
        state.constrain(buffer[3] == ord("{"))

        # Optional: Add more constraints if we know more about the flag format
        # For example, flags often end with "}"
        # state.constrain(buffer[INPUT_SIZE-1] == ord("}"))

        # Write our symbolic buffer to the global input location
        state.cpu.write_bytes(INPUT_ADDR, buffer)

        # Skip the strncpy and jump to the actual check
        # This avoids dealing with actual I/O operations
        state.cpu.EIP = 0x4005BD

    @m.hook(0x400850)  # Failure function
    def hook_failure(state):
        """
        Hook the failure path to abandon unsuccessful attempts.
        This significantly speeds up exploration.
        """
        print("  [-] Invalid input detected - abandoning path")
        state.abandon()

    @m.hook(0x400724)  # Success function
    def hook_success(state):
        """
        Hook the success path - we found the flag!
        """
        print("\n🎉 Success state reached! Solving for flag...")

        # Solve for the concrete input values
        # Note: For complex constraints, this might take a while
        solution = state.solve_buffer(INPUT_ADDR, INPUT_SIZE)

        # Convert to string
        flag = "".join(map(chr, solution))
        print(f"\n✅ FLAG FOUND: {flag}")

        # Store in context
        with m.locked_context() as ctx:
            ctx["solved"] = True
            ctx["flag"] = flag

        # No need to continue execution
        m.kill()

    # Run the symbolic execution
    print("\nStarting symbolic execution...")
    print("This may take a moment as Manticore explores different paths...")

    # Enable profiling for performance insights (optional)
    m.should_profile = True

    # Run the exploration
    m.run()

    # Check if we found the solution
    if m.context["solved"]:
        return m.context["flag"]
    else:
        print("\n❌ No solution found")
        print("The symbolic execution may have timed out or hit a limitation")
        return None


def main():
    """Main function to run the solver"""
    print("This example demonstrates solving a real CTF challenge using")
    print("symbolic execution without manually reverse engineering the binary.\n")

    flag = solve_unbreakable()

    if flag:
        # Verify it's the expected flag
        expected = "CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}"
        if flag == expected:
            print("\n✅ Verification: Flag matches expected solution!")
        else:
            print("\n⚠️  Found different flag than expected")
            print(f"   Expected: {expected}")
            print(f"   Found:    {flag}")

        print("\n" + "=" * 70)
        print("💡 Key Techniques Used:")
        print("=" * 70)
        print("1. Symbolic buffer creation for unknown input")
        print("2. Constraint application for known flag format")
        print("3. Execution path hooks to guide exploration")
        print("4. Abandoning invalid paths early for efficiency")
        print("5. Concrete value extraction from symbolic execution")

        return 0
    else:
        return 1


if __name__ == "__main__":
    sys.exit(main())
