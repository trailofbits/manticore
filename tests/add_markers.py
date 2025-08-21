#!/usr/bin/env python3
"""
Conservative script to add markers to test files.
Only marks the most obvious cases to avoid breaking anything.
"""

import os
from pathlib import Path

# Map of test files to their markers - ONLY THE MOST OBVIOUS ONES
MARKER_MAP = {
    # Generated tests - DO NOT EDIT these files
    'native/test_x86.py': ['generated_test', 'slow_test'],
    'native/test_cpu_automatic.py': ['generated_test', 'slow_test'],
    'native/test_aarch64cpu.py': ['generated_test', 'slow_test'],
    'native/test_x86_pcmpxstrx.py': ['generated_test', 'slow_test'],
    
    # Obvious integration test
    'native/test_integration_native.py': ['integration_test'],
    
    # Obvious benchmark
    'ethereum_bench/test_consensys_benchmark.py': ['benchmark'],
}

def add_markers_to_file(filepath, markers):
    """Add markers to a test file conservatively."""
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    # Check if already has markers import
    has_markers_import = any('from tests.markers import' in line for line in lines)
    if has_markers_import:
        print(f"  ⚠️  {filepath} already has markers import, skipping")
        return False
    
    # Find where to insert import (after other imports)
    import_line = -1
    for i, line in enumerate(lines):
        if line.startswith('import ') or line.startswith('from '):
            import_line = i
    
    if import_line == -1:
        print(f"  ⚠️  {filepath} has no imports, needs manual review")
        return False
    
    # Build import statement
    marker_names = ', '.join(markers)
    import_statement = f"from tests.markers import {marker_names}\n"
    
    # Insert after last import
    lines.insert(import_line + 1, "\n")
    lines.insert(import_line + 1, import_statement)
    
    # Find test classes to mark
    classes_marked = 0
    for i, line in enumerate(lines):
        if line.startswith('class ') and ('Test' in line or 'test' in line):
            # Add marker decorator before class
            indent = len(line) - len(line.lstrip())
            for marker in reversed(markers):
                lines.insert(i + classes_marked, ' ' * indent + f"@{marker}\n")
                classes_marked += 1
    
    if classes_marked == 0:
        print(f"  ⚠️  {filepath} has no test classes found")
        return False
    
    # Write back
    with open(filepath, 'w') as f:
        f.writelines(lines)
    
    print(f"  ✅ Added {markers} to {filepath}")
    return True

def main():
    print("CONSERVATIVE MARKER ADDITION")
    print("=" * 70)
    print("This script will ONLY mark:")
    print("  - Obviously generated tests (100k+ lines)")
    print("  - Explicit integration tests (have 'integration' in name)")
    print("  - Explicit benchmarks (have 'benchmark' in name)")
    print()
    
    response = input("Continue? (y/n): ")
    if response.lower() != 'y':
        print("Aborted.")
        return
    
    success = 0
    failed = 0
    
    for rel_path, markers in MARKER_MAP.items():
        filepath = Path('tests') / rel_path
        if not filepath.exists():
            print(f"  ❌ {filepath} not found")
            failed += 1
            continue
        
        if add_markers_to_file(filepath, markers):
            success += 1
        else:
            failed += 1
    
    print()
    print(f"RESULTS: {success} files marked, {failed} skipped/failed")
    print()
    print("NEXT STEPS:")
    print("1. Review the changes with: git diff tests/")
    print("2. Run tests to ensure nothing broke: pytest tests/")
    print("3. Commit if everything works")

if __name__ == '__main__':
    main()