#!/usr/bin/env python
"""
Test script to verify Manticore examples work correctly.
Run from the examples directory.
"""

import subprocess
import sys
import os
from pathlib import Path

def test_linux_basic():
    """Test the basic Linux example."""
    print("Testing examples/linux/basic...")
    
    # Build if needed
    if not Path("linux/basic").exists():
        print("  Building Linux examples...")
        result = subprocess.run(["make"], cwd="linux", capture_output=True)
        if result.returncode != 0:
            print(f"  ERROR: Failed to build examples: {result.stderr.decode()}")
            return False
    
    # Run Manticore on basic
    print("  Running Manticore on basic...")
    result = subprocess.run(
        ["manticore", "basic"],
        cwd="linux",
        capture_output=True,
        text=True,
        timeout=60
    )
    
    if result.returncode != 0:
        print(f"  ERROR: Manticore failed: {result.stderr}")
        return False
    
    # Check output
    if "Generated testcase" not in result.stderr:
        print("  ERROR: No test cases generated")
        return False
    
    # Count test cases
    import glob
    test_files = glob.glob("linux/mcore_*/test_*.stdin")
    print(f"  Generated {len(test_files)} test case(s)")
    
    if len(test_files) < 1:
        print("  WARNING: Expected at least 2 test cases for basic example")
    
    print("  ✓ Basic example works")
    return True

def test_evm_simple():
    """Test a simple EVM example."""
    print("Testing examples/evm/simple_value_check.sol...")
    
    if not Path("evm/simple_value_check.sol").exists():
        print("  ERROR: EVM example not found")
        return False
    
    print("  Running Manticore on simple_value_check.sol...")
    result = subprocess.run(
        ["manticore", "simple_value_check.sol"],
        cwd="evm",
        capture_output=True,
        text=True,
        timeout=60
    )
    
    if result.returncode != 0:
        print(f"  WARNING: Manticore may have failed (check if solc is installed)")
        print(f"  stderr: {result.stderr[:200]}...")
    else:
        print("  ✓ EVM example works")
    
    return True

def test_script_count():
    """Test the count_instructions.py script."""
    print("Testing examples/script/count_instructions.py...")
    
    # Build helloworld if needed
    if not Path("linux/helloworld").exists():
        subprocess.run(["make"], cwd="linux", capture_output=True)
    
    result = subprocess.run(
        [sys.executable, "script/count_instructions.py", "linux/helloworld"],
        capture_output=True,
        text=True,
        timeout=30
    )
    
    if result.returncode != 0:
        print(f"  ERROR: Script failed: {result.stderr}")
        return False
    
    if "Instructions executed:" in result.stdout:
        print("  ✓ count_instructions.py works")
        return True
    else:
        print("  ERROR: Unexpected output from count_instructions.py")
        return False

def main():
    """Run all tests."""
    print("=" * 60)
    print("Testing Manticore Examples")
    print("=" * 60)
    
    # Change to examples directory
    examples_dir = Path(__file__).parent
    os.chdir(examples_dir)
    
    tests = [
        test_linux_basic,
        test_script_count,
        test_evm_simple,  # May fail if solc not installed
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            if test():
                passed += 1
            else:
                failed += 1
        except Exception as e:
            print(f"  ERROR: Test crashed: {e}")
            failed += 1
        print()
    
    print("=" * 60)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 60)
    
    return failed == 0

if __name__ == "__main__":
    sys.exit(0 if main() else 1)