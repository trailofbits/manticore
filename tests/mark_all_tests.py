#!/usr/bin/env python3
"""
Mark all test files with appropriate markers based on analysis.
This script actually modifies the files.
"""

import os
import re
from pathlib import Path

# Comprehensive marker map based on our analysis
MARKER_MAP = {
    # Generated tests - massive files
    'native/test_x86.py': {
        'markers': ['generated_test', 'slow_test', 'native_test'],
        'class_name': 'CPUTest'
    },
    'native/test_cpu_automatic.py': {
        'markers': ['generated_test', 'slow_test', 'native_test'],
        'class_name': 'CPUTest'
    },
    'native/test_aarch64cpu.py': {
        'markers': ['generated_test', 'slow_test', 'native_test'],
        'class_name': 'Aarch64CPUTest'
    },
    'native/test_x86_pcmpxstrx.py': {
        'markers': ['generated_test', 'slow_test', 'native_test'],
        'class_name': 'X86PcmpxstrxInstructions'
    },
    
    # Integration tests
    'native/test_integration_native.py': {
        'markers': ['integration_test', 'native_test'],
        'class_name': None  # Will find all test classes
    },
    
    # Benchmark
    'ethereum_bench/test_consensys_benchmark.py': {
        'markers': ['benchmark', 'ethereum_test'],
        'class_name': None
    },
    
    # Slow tests (>1000 lines)
    'native/test_slam_regre.py': {
        'markers': ['slow_test', 'native_test'],
        'class_name': None
    },
    'native/test_dyn.py': {
        'markers': ['slow_test', 'native_test'],
        'class_name': None
    },
    'native/test_armv7cpu.py': {
        'markers': ['slow_test', 'native_test'],
        'class_name': None
    },
    'ethereum/test_general.py': {
        'markers': ['slow_test', 'ethereum_test'],
        'class_name': None
    },
    'native/test_armv7unicorn.py': {
        'markers': ['slow_test', 'native_test', 'linux_only'],
        'class_name': None
    },
    'native/test_memory.py': {
        'markers': ['slow_test', 'native_test'],
        'class_name': None
    },
    
    # Platform-specific
    'native/test_linux.py': {
        'markers': ['linux_only', 'native_test'],
        'class_name': None
    },
    'native/test_syscalls.py': {
        'markers': ['linux_only', 'native_test'],
        'class_name': None
    },
    
    # Component tests - just add component markers
    'ethereum/test_detectors.py': {
        'markers': ['ethereum_test'],
        'class_name': None
    },
    'ethereum/test_plugins.py': {
        'markers': ['ethereum_test'],
        'class_name': None
    },
    'ethereum/test_regressions.py': {
        'markers': ['ethereum_test'],
        'class_name': None
    },
    'ethereum/test_sha3.py': {
        'markers': ['ethereum_test'],
        'class_name': None
    },
    'wasm/test_callbacks.skip': {
        'markers': ['wasm_test'],
        'class_name': None
    },
    'wasm/test_examples.py': {
        'markers': ['wasm_test'],
        'class_name': None
    },
    'wasm/test_execution.py': {
        'markers': ['wasm_test'],
        'class_name': None
    },
    'wasm/test_stack_supplemental.py': {
        'markers': ['wasm_test'],
        'class_name': None
    },
    'wasm/test_state_saving.py': {
        'markers': ['wasm_test'],
        'class_name': None
    },
}

def add_markers_to_file(filepath, markers, specific_class=None):
    """Add markers to a test file."""
    print(f"Processing {filepath}...")
    
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception as e:
        print(f"  ❌ Error reading file: {e}")
        return False
    
    # Check if already has markers
    if 'from tests.markers import' in content:
        print(f"  ⚠️  Already has markers import, skipping")
        return False
    
    # Find import section
    lines = content.split('\n')
    last_import_idx = -1
    for i, line in enumerate(lines):
        if line.startswith('import ') or line.startswith('from '):
            last_import_idx = i
    
    if last_import_idx == -1:
        print(f"  ⚠️  No imports found, adding at top")
        last_import_idx = 0
    
    # Add import
    marker_import = f"from tests.markers import {', '.join(markers)}"
    lines.insert(last_import_idx + 1, marker_import)
    
    # Find and mark test classes
    marked_classes = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        # Look for class definitions
        if re.match(r'^class\s+\w*[Tt]est\w*.*:', line):
            class_match = re.match(r'^class\s+(\w+).*:', line)
            if class_match:
                class_name = class_match.group(1)
                # If specific class is specified, only mark that one
                if specific_class and class_name != specific_class:
                    i += 1
                    continue
                
                # Add decorators before the class
                for marker in reversed(markers):
                    lines.insert(i, f"@{marker}")
                    i += 1
                marked_classes += 1
                print(f"  ✓ Marked class {class_name}")
        i += 1
    
    if marked_classes == 0:
        print(f"  ⚠️  No test classes found to mark")
        # Remove the import we added
        lines = [l for l in lines if marker_import not in l]
    
    # Write back
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
        print(f"  ✅ Successfully marked {marked_classes} classes")
        return True
    except Exception as e:
        print(f"  ❌ Error writing file: {e}")
        return False

def main():
    print("MARKING ALL TEST FILES")
    print("=" * 70)
    
    # Count what we're about to do
    total_files = len(MARKER_MAP)
    print(f"Will process {total_files} test files")
    print()
    
    response = input("This will modify test files. Continue? (y/n): ")
    if response.lower() != 'y':
        print("Aborted.")
        return
    
    success = 0
    failed = 0
    
    for rel_path, config in MARKER_MAP.items():
        filepath = Path('tests') / rel_path
        if not filepath.exists():
            print(f"  ❌ {filepath} not found")
            failed += 1
            continue
        
        if add_markers_to_file(
            filepath, 
            config['markers'], 
            config.get('class_name')
        ):
            success += 1
        else:
            failed += 1
    
    print()
    print("=" * 70)
    print(f"RESULTS: {success} files marked, {failed} skipped/failed")
    print()
    print("NEXT STEPS:")
    print("1. Review changes: git diff tests/")
    print("2. Test markers: pytest --markers")
    print("3. Run tests: pytest tests/ -k 'not slow_test'")
    print("4. If all good: git add tests/ && git commit -m 'Add test markers'")

if __name__ == '__main__':
    main()