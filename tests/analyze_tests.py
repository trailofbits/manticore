#!/usr/bin/env python3
"""
Analyze test files to suggest appropriate markers.
This script does NOT modify files - it only analyzes and suggests.
"""

import os
import ast
from pathlib import Path

def analyze_test_file(filepath):
    """Analyze a test file and suggest markers."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    filename = os.path.basename(filepath)
    relpath = os.path.relpath(filepath, 'tests')
    markers = []
    
    # Check for obvious patterns
    if 'integration' in filename.lower():
        markers.append('integration_test')
    
    if 'benchmark' in filename.lower() or 'bench' in filename.lower():
        markers.append('benchmark')
    
    # Check file size for generated tests
    lines = content.count('\n')
    if lines > 10000:
        markers.append('generated_test')
        markers.append('slow_test')
    elif lines > 1000:
        markers.append('slow_test')
    
    # Check for platform-specific code
    if 'linux' in content.lower() and 'darwin' not in content.lower():
        if 'skip' in content or 'Linux' in content:
            markers.append('linux_only')
    
    # Component-based markers
    filepath_str = str(filepath)
    if 'ethereum' in filepath_str:
        markers.append('ethereum_test')
    elif 'native' in filepath_str:
        markers.append('native_test')
    elif 'wasm' in filepath_str:
        markers.append('wasm_test')
    
    # Check for network operations
    if any(word in content for word in ['socket', 'urllib', 'requests', 'http']):
        markers.append('requires_network')
    
    # Default to unit test if no integration marker
    if 'integration_test' not in markers and 'benchmark' not in markers:
        markers.append('unit_test')
    
    return {
        'file': relpath,
        'lines': lines,
        'markers': markers
    }

def main():
    test_files = Path('tests').glob('**/test_*.py')
    results = []
    
    for filepath in sorted(test_files):
        if '__pycache__' in str(filepath):
            continue
        analysis = analyze_test_file(filepath)
        results.append(analysis)
    
    # Print analysis
    print("TEST FILE ANALYSIS")
    print("=" * 70)
    
    # Group by suggested markers
    generated = []
    integration = []
    benchmarks = []
    slow = []
    platform_specific = []
    regular = []
    
    for r in results:
        if 'generated_test' in r['markers']:
            generated.append(r)
        elif 'integration_test' in r['markers']:
            integration.append(r)
        elif 'benchmark' in r['markers']:
            benchmarks.append(r)
        elif 'slow_test' in r['markers']:
            slow.append(r)
        elif 'linux_only' in r['markers']:
            platform_specific.append(r)
        else:
            regular.append(r)
    
    if generated:
        print("\n📊 GENERATED TESTS (DO NOT EDIT):")
        for r in generated:
            print(f"  {r['file']} ({r['lines']:,} lines)")
            print(f"    Markers: {', '.join(r['markers'])}")
    
    if integration:
        print("\n🔗 INTEGRATION TESTS:")
        for r in integration:
            print(f"  {r['file']} ({r['lines']} lines)")
            print(f"    Markers: {', '.join(r['markers'])}")
    
    if benchmarks:
        print("\n⚡ BENCHMARK TESTS:")
        for r in benchmarks:
            print(f"  {r['file']} ({r['lines']} lines)")
            print(f"    Markers: {', '.join(r['markers'])}")
    
    if slow:
        print("\n🐢 SLOW TESTS:")
        for r in slow:
            print(f"  {r['file']} ({r['lines']} lines)")
            print(f"    Markers: {', '.join(r['markers'])}")
    
    if platform_specific:
        print("\n🖥️ PLATFORM-SPECIFIC TESTS:")
        for r in platform_specific:
            print(f"  {r['file']} ({r['lines']} lines)")
            print(f"    Markers: {', '.join(r['markers'])}")
    
    print(f"\n📈 SUMMARY:")
    print(f"  Total test files: {len(results)}")
    print(f"  Generated: {len(generated)}")
    print(f"  Integration: {len(integration)}")
    print(f"  Benchmarks: {len(benchmarks)}")
    print(f"  Slow: {len(slow)}")
    print(f"  Platform-specific: {len(platform_specific)}")
    print(f"  Regular unit tests: {len(regular)}")
    
    print("\n⚠️  This analysis is based on heuristics.")
    print("Review suggestions before applying markers.")

if __name__ == '__main__':
    main()