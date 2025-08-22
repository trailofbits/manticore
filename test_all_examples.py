#!/usr/bin/env python3
"""
Comprehensive test of all manticore-examples to determine macOS compatibility
"""

import os
import sys
import subprocess
import tempfile
import shutil
from pathlib import Path
import json


def test_example(script_path, timeout=30):
    """Run a single example and categorize the result"""
    try:
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=script_path.parent,
            capture_output=True,
            text=True,
            timeout=timeout,
        )

        output = result.stdout + result.stderr

        # Categorize the failure/success
        if "CTF{" in output or "flag" in output.lower() or "success" in output.lower():
            return "SUCCESS", "Found flag or success indicator"
        elif "Binary" in output and "not supported" in output:
            return "PLATFORM", "Binary not supported on macOS"
        elif "NoAliveStates" in output:
            return "NO_STATES", "No alive states - contract/binary issue"
        elif "AssertionError" in output:
            return "ASSERT", "Assertion failed - logic issue"
        elif "FileNotFoundError" in output:
            return "MISSING", "Missing file"
        elif "TypeError" in output or "AttributeError" in output:
            return "API", "API compatibility issue"
        elif "mmap" in output.lower():
            return "MMAP", "Memory mapping issue (Linux-specific)"
        elif result.returncode == 0:
            return "SUCCESS", "Completed without error"
        else:
            return "UNKNOWN", f"Return code {result.returncode}"

    except subprocess.TimeoutExpired:
        return "TIMEOUT", f"Exceeded {timeout} seconds"
    except Exception as e:
        return "ERROR", str(e)


def fix_paths(examples_dir):
    """Fix all path issues in examples"""
    fixes = [
        # test_ais3_crackme
        (
            "test_ais3_crackme/test_ais3_crackme.py",
            'from manticore.native import Manticore\n\n    m = Manticore("test_ais3_crackme/ais3_crackme"',
            'from manticore.native import Manticore\n    import os\n\n    script_dir = os.path.dirname(os.path.abspath(__file__))\n    binary_path = os.path.join(script_dir, "ais3_crackme")\n    m = Manticore(binary_path',
        ),
        # test_internetwache15-re60
        (
            "test_internetwache15-re60/test_internetwache15-re60.py",
            '    if __name__ == "__main__":\n        binary = "./filechecker"\n    else:\n        binary = "./test_internetwache15-re60/filechecker"\n\n    m = Manticore(binary)',
            '    import os\n    script_dir = os.path.dirname(os.path.abspath(__file__))\n    binary = os.path.join(script_dir, "filechecker")\n    m = Manticore(binary)',
        ),
        # test_manticore_challenge
        (
            "test_manticore_challenge/test_manticore_challenge.py",
            '    file = ""\n    if __name__ == "__main__":\n        file = "manticore_challenge"\n    else:\n        file = "./test_manticore_challenge/manticore_challenge"',
            '    import os\n    script_dir = os.path.dirname(os.path.abspath(__file__))\n    file = os.path.join(script_dir, "manticore_challenge")',
        ),
        # test_polyswarm_challenge
        (
            "test_polyswarm_challenge/test_polyswarm_challenge.py",
            '    file = ""\n    if __name__ == "__main__":\n        file = "winnerlog.bin"\n    else:\n        file = "test_polyswarm_challenge/winnerlog.bin"',
            '    import os\n    script_dir = os.path.dirname(os.path.abspath(__file__))\n    file = os.path.join(script_dir, "winnerlog.bin")',
        ),
        # RPISEC_MBE labs
        (
            "RPISEC_MBE/lab1A.py",
            'm = Manticore("./lab1A")',
            'import os\nscript_dir = os.path.dirname(os.path.abspath(__file__))\nm = Manticore(os.path.join(script_dir, "lab1A"))',
        ),
        (
            "RPISEC_MBE/lab1B.py",
            'm = Manticore("./lab1B")',
            'import os\nscript_dir = os.path.dirname(os.path.abspath(__file__))\nm = Manticore(os.path.join(script_dir, "lab1B"))',
        ),
    ]

    for file_path, old_text, new_text in fixes:
        full_path = examples_dir / file_path
        if full_path.exists():
            content = full_path.read_text()
            if old_text in content:
                content = content.replace(old_text, new_text)
                full_path.write_text(content)
                print(f"  Fixed: {file_path}")


def main():
    print("=" * 70)
    print("Comprehensive Manticore Examples Test on macOS")
    print("=" * 70)

    with tempfile.TemporaryDirectory() as tmpdir:
        examples_dir = Path(tmpdir) / "manticore-examples"

        # Clone repository
        print("Cloning manticore-examples...")
        result = subprocess.run(
            [
                "git",
                "clone",
                "--depth",
                "1",
                "https://github.com/trailofbits/manticore-examples",
                str(examples_dir),
            ],
            capture_output=True,
            text=True,
        )

        if result.returncode != 0:
            print(f"Failed to clone: {result.stderr}")
            return 1

        # Fix paths
        print("\nFixing path issues...")
        fix_paths(examples_dir)

        # List all test scripts
        test_scripts = [
            "test_google2016_unbreakable/test_google2016_unbreakable.py",
            "test_ais3_crackme/test_ais3_crackme.py",
            "test_manticore_challenge/test_manticore_challenge.py",
            "test_internetwache15-re60/test_internetwache15-re60.py",
            "test_hxp2018_angrme/test_hxp2018_angrme.py",
            "test_pwnable_collision/test_pwnable_collision.py",
            "test_polyswarm_challenge/test_polyswarm_challenge.py",
            "test_exploit_generation_example/test_crash_analysis.py",
            "test_exploit_generation_example/test_record.py",
            "RPISEC_MBE/lab1A.py",
            "RPISEC_MBE/lab1B.py",
        ]

        results = {}

        print("\nTesting examples...")
        print("-" * 70)

        for script in test_scripts:
            script_path = examples_dir / script
            if script_path.exists():
                print(f"Testing: {script:<50}", end=" ")
                status, message = test_example(script_path)
                results[script] = {"status": status, "message": message}

                # Print status with color
                if status == "SUCCESS":
                    print(f"✅ {status}")
                elif status in ["PLATFORM", "MMAP"]:
                    print(f"🚫 {status}")
                elif status == "API":
                    print(f"⚠️  {status}")
                else:
                    print(f"❌ {status}")
            else:
                print(f"Testing: {script:<50} ❓ NOT FOUND")
                results[script] = {"status": "NOT_FOUND", "message": "Script not found"}

        # Summary
        print("\n" + "=" * 70)
        print("Summary by Category")
        print("=" * 70)

        categories = {}
        for script, result in results.items():
            status = result["status"]
            if status not in categories:
                categories[status] = []
            categories[status].append(script)

        for status in [
            "SUCCESS",
            "API",
            "PLATFORM",
            "MMAP",
            "NO_STATES",
            "ASSERT",
            "TIMEOUT",
            "ERROR",
            "UNKNOWN",
            "NOT_FOUND",
        ]:
            if status in categories:
                print(f"\n{status} ({len(categories[status])} examples):")
                for script in categories[status]:
                    print(f"  - {script}")
                    if results[script]["message"]:
                        print(f"    ({results[script]['message']})")

        # Recommendations
        print("\n" + "=" * 70)
        print("Recommendations for macOS Compatibility")
        print("=" * 70)

        if "SUCCESS" in categories:
            print("\n✅ Working Examples (can be used as tests):")
            for script in categories["SUCCESS"]:
                print(f"  - {script}")

        if "API" in categories:
            print("\n⚠️  API Issues (need code updates):")
            for script in categories["API"]:
                print(f"  - {script}")

        print("\n🚫 Platform Issues (Linux ELF binaries - won't work on macOS natively):")
        for status in ["PLATFORM", "MMAP"]:
            if status in categories:
                for script in categories[status]:
                    print(f"  - {script}")

        print("\n💡 Potential Solutions:")
        print("  1. Use Docker/Linux VM for Linux binary examples")
        print("  2. Port examples to use macOS binaries (Mach-O)")
        print("  3. Focus on Ethereum/WASM examples (platform-independent)")
        print("  4. Create synthetic test binaries that work cross-platform")

        # Save results to JSON
        results_file = Path("manticore_examples_test_results.json")
        with open(results_file, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\n📊 Detailed results saved to: {results_file}")

        return 0


if __name__ == "__main__":
    sys.exit(main())
