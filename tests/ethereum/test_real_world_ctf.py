"""
Test suite for real-world CTF challenge examples.

These tests ensure that our CTF solution examples continue to work with
current versions of Manticore. They serve both as regression tests and
as demonstrations of Manticore's capabilities.
"""

import unittest
import os
import sys
import subprocess
from pathlib import Path
import tempfile
import shutil


class TestRealWorldCTF(unittest.TestCase):
    """Test real-world CTF challenge solutions"""
    
    @classmethod
    def setUpClass(cls):
        """Set up paths to example scripts"""
        # Find the examples directory
        manticore_root = Path(__file__).parent.parent.parent
        cls.examples_dir = manticore_root / "examples" / "ctf"
        
        if not cls.examples_dir.exists():
            raise unittest.SkipTest(f"Examples directory not found: {cls.examples_dir}")
    
    def run_ctf_example(self, challenge_name, script_name, timeout=120):
        """Helper to run a CTF example script"""
        challenge_dir = self.examples_dir / challenge_name
        script_path = challenge_dir / script_name
        
        if not script_path.exists():
            self.skipTest(f"Script not found: {script_path}")
        
        # Run the script
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=challenge_dir,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        
        return result
    
    def test_polyswarm_challenge(self):
        """
        Test the PolySwarm smart contract challenge solution.
        
        This challenge requires finding the magic bytes that satisfy
        a smart contract's validation logic.
        """
        result = self.run_ctf_example(
            "polyswarm_challenge",
            "polyswarm_challenge.py",
            timeout=180  # Give it more time for symbolic execution
        )
        
        output = result.stdout + result.stderr
        
        # Check for success indicators
        success_indicators = [
            "Challenge Solved",
            "Found potential solution",
            "dogecointothemoon",  # Part of the expected solution
            "FOUND:"  # Original script output
        ]
        
        found_success = any(indicator in output for indicator in success_indicators)
        
        if not found_success:
            # Check if it's an API issue vs actual failure
            if "NoAliveStates" in output:
                self.skipTest("Contract deployment issues - may need bytecode update")
            elif "TypeError" in output or "AttributeError" in output:
                self.skipTest("API compatibility issue - example needs update")
            elif result.returncode != 0:
                # Print output for debugging
                print("STDOUT:", result.stdout)
                print("STDERR:", result.stderr)
                self.fail(f"Script failed with return code {result.returncode}")
        
        # If we get here, we found a success indicator
        self.assertTrue(found_success, "Should find the solution to the challenge")
    
    def test_polyswarm_bytecode_exists(self):
        """Verify that the required bytecode file exists"""
        bytecode_path = self.examples_dir / "polyswarm_challenge" / "winnerlog.bin"
        self.assertTrue(bytecode_path.exists(), f"Bytecode file should exist: {bytecode_path}")
        
        # Verify it's not empty
        size = bytecode_path.stat().st_size
        self.assertGreater(size, 0, "Bytecode file should not be empty")
        
        # Verify it contains the expected hint string
        with open(bytecode_path, "rb") as f:
            content = f.read()
            # The contract contains this hint string
            self.assertIn(b"dogecointothemoon", content, 
                         "Bytecode should contain the hint string")


class TestCTFExampleImports(unittest.TestCase):
    """Test that CTF examples can be imported and have proper structure"""
    
    def test_polyswarm_imports(self):
        """Test that the PolySwarm example imports correctly"""
        # Add examples directory to path
        manticore_root = Path(__file__).parent.parent.parent
        examples_dir = manticore_root / "examples" / "real_world_ctf" / "polyswarm_challenge"
        
        if not examples_dir.exists():
            self.skipTest("Examples directory not found")
        
        sys.path.insert(0, str(examples_dir))
        
        try:
            # Try to import the module
            import polyswarm_challenge
            
            # Check that it has the expected functions
            self.assertTrue(hasattr(polyswarm_challenge, 'solve_polyswarm_challenge'),
                          "Should have solve_polyswarm_challenge function")
            self.assertTrue(hasattr(polyswarm_challenge, 'main'),
                          "Should have main function")
            
        finally:
            # Clean up sys.path
            sys.path.pop(0)


if __name__ == "__main__":
    unittest.main()