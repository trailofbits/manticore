#!/usr/bin/env python3
"""
Simplified PolySwarm Challenge - Demonstrating the Core Concept

This is a simplified version that demonstrates the key insight of the challenge:
finding the magic bytes "dogecointothemoonlambosoondudes!" through symbolic execution.

The original challenge had a smart contract that checked if input data matched
a specific pattern. This example shows how Manticore can find such patterns.
"""

from manticore.core.smtlib import ConstraintSet, Operators
from manticore.core.smtlib.solver import Z3Solver
import binascii


def find_magic_bytes():
    """
    Demonstrate finding magic bytes through symbolic execution.

    In the real challenge, the contract checks if the input matches
    "dogecointothemoonlambosoondudes!" but this is obfuscated in the bytecode.
    """
    print("=" * 70)
    print("PolySwarm Challenge - Core Concept Demo")
    print("=" * 70)
    print("\nScenario: A smart contract checks if input[i] XOR key[i] == target[i]")
    print("We know the target pattern but not the input needed.\n")

    # The target string we're trying to match (what the contract expects)
    target = b"dogecointothemoonlambosoondudes!"

    # Simulate a simple obfuscation: XOR with a key
    # In the real contract, this is more complex
    xor_key = b"\x00" * len(target)  # Simple case: no XOR (key = 0)

    # Create constraint set
    constraints = ConstraintSet()
    solver = Z3Solver.instance()

    # Create symbolic bytes for our input
    symbolic_input = []
    for i in range(len(target)):
        byte_var = constraints.new_bitvec(8, name=f"input_byte_{i}")
        symbolic_input.append(byte_var)

        # Add constraint: input[i] XOR key[i] must equal target[i]
        constraints.add(byte_var ^ xor_key[i] == target[i])

        # Additional constraint: input must be printable ASCII (optional)
        constraints.add(byte_var >= 0x20)
        constraints.add(byte_var <= 0x7E)

    print("Solving constraints...")
    print(f"Looking for {len(target)} bytes that satisfy the contract\n")

    if solver.check(constraints):
        # Get concrete values
        solution = bytes([solver.get_value(constraints, b) for b in symbolic_input])

        print("✅ Found solution!")
        print(f"   Hex: {binascii.hexlify(solution).decode()}")
        print(f"   ASCII: {solution.decode('ascii')}")

        # Verify
        result = bytes([solution[i] ^ xor_key[i] for i in range(len(solution))])
        assert result == target, "Verification failed!"
        print("\n   Verification: Input XOR Key = Target ✓")

        return solution
    else:
        print("❌ No solution found")
        return None


def demonstrate_complex_case():
    """
    Demonstrate a more complex case with actual XOR obfuscation.
    This is closer to what the real contract does.
    """
    print("\n" + "=" * 70)
    print("Advanced Case - With XOR Obfuscation")
    print("=" * 70)

    # The target result after XOR
    target = b"dogecointothemoonlambosoondudes!"

    # A "secret" XOR key (in the real contract, this is derived from storage)
    xor_key = bytes([0x42, 0x13, 0x37] * 11)  # Repeating pattern
    xor_key = xor_key[: len(target)]  # Trim to target length

    print(f"\nThe contract has a hidden XOR key: {binascii.hexlify(xor_key).decode()}")
    print("We need to find input such that: input XOR key = target\n")

    # Create constraints
    constraints = ConstraintSet()
    solver = Z3Solver.instance()

    symbolic_input = []
    for i in range(len(target)):
        byte_var = constraints.new_bitvec(8, name=f"adv_input_{i}")
        symbolic_input.append(byte_var)

        # Constraint: input[i] XOR key[i] == target[i]
        constraints.add((byte_var ^ xor_key[i]) == target[i])

    print("Using symbolic execution to find the input...")

    if solver.check(constraints):
        solution = bytes([solver.get_value(constraints, b) for b in symbolic_input])

        print("✅ Found the magic input!")
        print(f"   Input (hex): {binascii.hexlify(solution).decode()}")

        # Try to print as ASCII if possible
        try:
            ascii_str = "".join(chr(b) if 32 <= b < 127 else f"\\x{b:02x}" for b in solution)
            print(f"   Input (mixed): {ascii_str}")
        except:
            pass

        # Verify
        result = bytes([solution[i] ^ xor_key[i] for i in range(len(solution))])
        print(f"\n   Verification: {result.decode('ascii')}")
        assert result == target, "Verification failed!"

        print("\n💡 This demonstrates how Manticore can reverse engineer obfuscated checks!")
        return solution
    else:
        print("❌ No solution found")
        return None


def main():
    """Run the demonstration"""
    print("This example demonstrates the core technique used to solve")
    print("the PolySwarm smart contract challenge.\n")

    # Simple case
    solution1 = find_magic_bytes()

    # Complex case with XOR
    solution2 = demonstrate_complex_case()

    if solution1 and solution2:
        print("\n" + "=" * 70)
        print("🎉 Success! Both demonstrations completed.")
        print("=" * 70)
        print("\nKey Takeaways:")
        print("1. Symbolic execution can find inputs that satisfy complex conditions")
        print("2. Even obfuscated checks (XOR, transformations) can be reversed")
        print("3. This technique works on real smart contract bytecode")
        print("4. The actual PolySwarm contract was more complex but used similar principles")
        return 0
    else:
        return 1


if __name__ == "__main__":
    import sys

    sys.exit(main())
