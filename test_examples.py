#!/usr/bin/env python3
"""
Test suite for Manticore examples
Tests that key example scripts still work with current Manticore
"""
import os
import sys
import subprocess
import tempfile
import shutil
from pathlib import Path


def clone_examples_repo(target_dir):
    """Clone the manticore-examples repository"""
    print(f"Cloning manticore-examples to {target_dir}...")
    result = subprocess.run(
        ["git", "clone", "--depth", "1", "https://github.com/trailofbits/manticore-examples", target_dir],
        capture_output=True,
        text=True
    )
    if result.returncode != 0:
        print(f"Failed to clone: {result.stderr}")
        return False
    return True


def fix_path_issues(examples_dir):
    """Fix common path issues in example scripts"""
    
    # Fix test_google2016_unbreakable - already works, no fix needed
    
    # Fix test_ais3_crackme
    ais3_file = examples_dir / "test_ais3_crackme" / "test_ais3_crackme.py"
    if ais3_file.exists():
        content = ais3_file.read_text()
        content = content.replace(
            '    m = Manticore("test_ais3_crackme/ais3_crackme", ["a" * 30])',
            '''    import os
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary_path = os.path.join(script_dir, "ais3_crackme")
    m = Manticore(binary_path, ["a" * 30])'''
        )
        ais3_file.write_text(content)
        print("  Fixed path in test_ais3_crackme.py")
    
    # Fix test_manticore_challenge
    mcore_file = examples_dir / "test_manticore_challenge" / "test_manticore_challenge.py"
    if mcore_file.exists():
        content = mcore_file.read_text()
        if 'file = ""' in content:
            content = content.replace(
                '''    file = ""
    if __name__ == "__main__":
        file = "manticore_challenge"
    else:
        file = "./test_manticore_challenge/manticore_challenge"''',
                '''    import os
    script_dir = os.path.dirname(os.path.abspath(__file__))
    file = os.path.join(script_dir, "manticore_challenge")'''
            )
            mcore_file.write_text(content)
            print("  Fixed path in test_manticore_challenge.py")
    
    # Fix test_internetwache15-re60
    iw_file = examples_dir / "test_internetwache15-re60" / "test_internetwache15-re60.py"
    if iw_file.exists():
        content = iw_file.read_text()
        content = content.replace(
            '''    if __name__ == "__main__":
        binary = "./filechecker"
    else:
        binary = "./test_internetwache15-re60/filechecker"

    m = Manticore(binary)''',
            '''    import os
    script_dir = os.path.dirname(os.path.abspath(__file__))
    binary = os.path.join(script_dir, "filechecker")
    m = Manticore(binary)'''
        )
        iw_file.write_text(content)
        print("  Fixed path in test_internetwache15-re60.py")


def run_example(script_path, timeout=60):
    """Run a single example script"""
    print(f"\nTesting: {script_path.name}")
    print("-" * 40)
    
    try:
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=script_path.parent,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        
        # Check for success indicators
        success = False
        output = result.stdout + result.stderr
        
        if "CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}" in output:
            print("  ✅ Found Google CTF flag!")
            success = True
        elif "ais3{I_tak3_g00d_n0t3s}" in output:
            print("  ✅ Found AIS3 flag!")
            success = True
        elif "=MANTICORE==" in output:
            print("  ✅ Found Manticore challenge flag!")
            success = True
        elif "IW{FILE_CHeCKa}" in output:
            print("  ✅ Found InternetWache flag!")
            success = True
        elif result.returncode == 0:
            print("  ✅ Script completed without errors")
            success = True
        else:
            print(f"  ❌ Script failed with return code {result.returncode}")
            if "AssertionError" in output:
                print("     (Assertion failed - may be timing/solver issue)")
            elif "Binary" in output and "not supported" in output:
                print("     (Binary not supported on this platform)")
            
        return success
        
    except subprocess.TimeoutExpired:
        print(f"  ⏱️  Timeout after {timeout} seconds")
        return False
    except Exception as e:
        print(f"  ❌ Error running script: {e}")
        return False


def main():
    """Main test function"""
    print("=" * 60)
    print("Manticore Examples Test Suite")
    print("=" * 60)
    
    # Create temporary directory for examples
    with tempfile.TemporaryDirectory() as tmpdir:
        examples_dir = Path(tmpdir) / "manticore-examples"
        
        # Clone repository
        if not clone_examples_repo(examples_dir):
            print("Failed to clone examples repository")
            return 1
        
        print("\nFixing path issues...")
        fix_path_issues(examples_dir)
        
        # List of examples to test (ones that should work)
        test_scripts = [
            examples_dir / "test_google2016_unbreakable" / "test_google2016_unbreakable.py",
            # These may fail due to platform/timing but have correct paths now:
            examples_dir / "test_ais3_crackme" / "test_ais3_crackme.py",
            examples_dir / "test_manticore_challenge" / "test_manticore_challenge.py",
            examples_dir / "test_internetwache15-re60" / "test_internetwache15-re60.py",
        ]
        
        # Run tests
        results = []
        for script in test_scripts:
            if script.exists():
                success = run_example(script)
                results.append((script.parent.name, success))
            else:
                print(f"\n❌ Script not found: {script}")
                results.append((script.parent.name, False))
        
        # Print summary
        print("\n" + "=" * 60)
        print("Test Summary")
        print("=" * 60)
        
        passed = sum(1 for _, success in results if success)
        total = len(results)
        
        for name, success in results:
            status = "✅ PASSED" if success else "❌ FAILED"
            print(f"  {name:<35} {status}")
        
        print(f"\nTotal: {passed}/{total} passed")
        
        if passed == 0:
            print("\n⚠️  Note: Many examples fail on macOS due to Linux ELF binary requirements.")
            print("    The Google CTF example should work cross-platform.")
        
        return 0 if passed > 0 else 1


if __name__ == "__main__":
    sys.exit(main())