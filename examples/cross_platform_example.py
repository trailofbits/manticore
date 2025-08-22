#!/usr/bin/env python3
"""
Cross-platform Manticore example that works on Linux, macOS, and Windows.
This demonstrates symbolic execution using Python-level operations rather than binary analysis.
"""

from manticore.ethereum import ManticoreEVM
from manticore.core.smtlib import Operators, solver


def test_ethereum_symbolic():
    """
    Test Ethereum smart contract with symbolic execution.
    This works on all platforms as it doesn't depend on binary formats.
    """
    print("=" * 60)
    print("Cross-Platform Ethereum Symbolic Execution Example")
    print("=" * 60)
    
    # Simple vulnerable contract (using compatible Solidity version)
    source_code = '''
    pragma solidity >=0.4.24;
    
    contract SimpleVault {
        mapping(address => uint256) private balances;
        uint256 public constant prize = 1000;
        
        function deposit() public payable {
            balances[msg.sender] += msg.value;
        }
        
        function withdraw(uint256 amount) public {
            require(balances[msg.sender] >= amount);
            balances[msg.sender] -= amount;
            msg.sender.transfer(amount);
        }
        
        function checkWin(uint256 guess) public view returns (bool) {
            // Vulnerable: predictable "random" number
            uint256 secret = uint256(keccak256(block.number)) % 100;
            return guess == secret;
        }
        
        function claimPrize(uint256 guess) public {
            require(checkWin(guess));
            msg.sender.transfer(prize);
        }
    }
    '''
    
    m = ManticoreEVM()
    
    # Create accounts
    owner = m.create_account(balance=10**18, name="owner")
    attacker = m.create_account(balance=10**16, name="attacker")
    
    # Deploy contract
    print("\nDeploying contract...")
    contract = m.solidity_create_contract(source_code, owner=owner, balance=2000)
    
    # Make a symbolic guess
    print("Creating symbolic value for guess...")
    symbolic_guess = m.make_symbolic_value(name="guess")
    
    # Try to win the prize with symbolic guess
    print("Attempting to claim prize with symbolic guess...")
    contract.claimPrize(symbolic_guess, caller=attacker)
    
    print("\nRunning symbolic execution...")
    m.run()
    
    # Check results
    print("\n" + "-" * 40)
    print("Results:")
    print("-" * 40)
    
    successful_states = []
    for state in m.all_states:
        # Check if attacker got the prize
        attacker_balance = state.platform.get_balance(attacker.address)
        if state.can_be_true(attacker_balance > 10**16):
            successful_states.append(state)
    
    if successful_states:
        print(f"✅ Found {len(successful_states)} successful attack state(s)!")
        
        # Get a concrete guess value that wins
        state = successful_states[0]
        guess_value = state.solve_one(symbolic_guess)
        print(f"   Winning guess value: {guess_value}")
        
        # Calculate what the secret would be
        print(f"   This means the secret was: {guess_value}")
        
        return True
    else:
        print("❌ No successful attack found")
        return False


def test_pure_symbolic():
    """
    Test pure symbolic execution without any binary or contract.
    This demonstrates Manticore's constraint solving capabilities.
    """
    print("\n" + "=" * 60)
    print("Cross-Platform Pure Symbolic Execution Example")
    print("=" * 60)
    
    from manticore.core.smtlib import ConstraintSet, Operators
    from manticore.core.smtlib.solver import Z3Solver
    from manticore.core.smtlib.expression import BitVecConstant
    
    # Create constraint set
    constraints = ConstraintSet()
    solver = Z3Solver.instance()
    
    # Create symbolic variables
    from manticore.core.smtlib import BitVecVariable
    password = constraints.new_bitvec(32, name="password")
    
    # Add constraints (reverse engineering a "password check")
    # Imagine this is: if ((password * 7 + 5) ^ 0x539) == 0x4D2
    result = (password * 7 + 5) ^ 0x539
    target = 0x4D2
    
    constraints.add(result == target)
    
    print("\nSolving constraint: ((password * 7 + 5) ^ 0x539) == 0x4D2")
    
    if solver.check(constraints):
        solution = solver.get_value(constraints, password)
        print(f"✅ Found password: {solution} (0x{solution:x})")
        
        # Verify
        check = ((solution * 7 + 5) ^ 0x539)
        print(f"   Verification: ((0x{solution:x} * 7 + 5) ^ 0x539) = 0x{check:x}")
        assert check == 0x4D2, "Verification failed!"
        return True
    else:
        print("❌ No solution found")
        return False


def test_symbolic_memory():
    """
    Test symbolic memory operations.
    This shows how Manticore can reason about memory symbolically.
    """
    print("\n" + "=" * 60)
    print("Cross-Platform Symbolic Memory Example")
    print("=" * 60)
    
    from manticore.core.smtlib import ConstraintSet
    from manticore.core.smtlib.solver import Z3Solver
    
    # Create constraint set (we'll use pure symbolic solving without Memory class)
    constraints = ConstraintSet()
    solver = Z3Solver.instance()
    
    # Create symbolic data
    symbolic_byte = constraints.new_bitvec(8, name="secret_byte")
    
    # Simulate writing symbolic data to memory
    address = 0x1000
    # In a real scenario, this would be written to memory
    # For this example, we'll just work with the symbolic value
    
    print(f"Simulated writing symbolic byte to address 0x{address:x}")
    
    # Add constraint: the byte must be a printable ASCII character
    constraints.add(symbolic_byte >= 0x20)  # Space
    constraints.add(symbolic_byte <= 0x7E)  # Tilde
    
    # Add another constraint: the byte XORed with 0x42 equals 0x01
    constraints.add((symbolic_byte ^ 0x42) == 0x01)
    
    print("Added constraints:")
    print("  - Byte must be printable ASCII (0x20 - 0x7E)")
    print("  - Byte XOR 0x42 must equal 0x01")
    
    if solver.check(constraints):
        solution = solver.get_value(constraints, symbolic_byte)
        print(f"\n✅ Found solution: 0x{solution:02x} ('{chr(solution)}')")
        
        # Verify
        print(f"   Verification: 0x{solution:02x} ^ 0x42 = 0x{solution ^ 0x42:02x}")
        assert (solution ^ 0x42) == 0x01, "Verification failed!"
        return True
    else:
        print("\n❌ No solution found")
        return False


def main():
    """Run all cross-platform examples"""
    results = []
    
    # Test pure symbolic execution (should always work)
    try:
        results.append(("Pure Symbolic", test_pure_symbolic()))
    except Exception as e:
        print(f"Error in pure symbolic test: {e}")
        results.append(("Pure Symbolic", False))
    
    # Test symbolic memory (should always work)
    try:
        results.append(("Symbolic Memory", test_symbolic_memory()))
    except Exception as e:
        print(f"Error in symbolic memory test: {e}")
        results.append(("Symbolic Memory", False))
    
    # Test Ethereum (requires solc but should work on all platforms)
    try:
        results.append(("Ethereum Symbolic", test_ethereum_symbolic()))
    except Exception as e:
        print(f"Error in Ethereum test: {e}")
        results.append(("Ethereum Symbolic", False))
    
    # Summary
    print("\n" + "=" * 60)
    print("Summary")
    print("=" * 60)
    
    for name, success in results:
        status = "✅ PASSED" if success else "❌ FAILED"
        print(f"{name:<20} {status}")
    
    passed = sum(1 for _, success in results if success)
    total = len(results)
    print(f"\nTotal: {passed}/{total} passed")
    
    return 0 if passed == total else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())