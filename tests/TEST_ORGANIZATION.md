# Test Organization Guide

## Current Structure (DO NOT CHANGE)

The test suite is organized by component, which works well for Manticore's architecture:

```
tests/
├── native/          # Native binary analysis tests (29 files)
│   ├── test_x86.py             # CPU instruction tests (115k lines - AUTO-GENERATED)
│   ├── test_cpu_automatic.py  # More CPU tests (46k lines - AUTO-GENERATED)
│   ├── test_integration_native.py  # Integration tests
│   └── binaries/               # Test binaries
├── ethereum/        # Smart contract tests (5 files)
│   ├── contracts/   # Test contracts
│   └── data/        # Test data
├── ethereum_bench/  # Benchmarks (1 file)
├── wasm/           # WebAssembly tests (4 files)
├── other/          # Utility tests (7 files)
└── auto_generators/ # Test generation scripts
```

## Test Categories

### Unit Tests
- Test individual components in isolation
- Most files in native/, ethereum/, wasm/
- Fast, focused, deterministic

### Integration Tests  
- Test multiple components together
- Files: test_integration_native.py
- Slower, test real workflows

### Generated Tests
- **DO NOT MANUALLY EDIT**
- test_x86.py, test_cpu_automatic.py
- Generated from CPU specifications
- Critical for instruction correctness

## Best Practices

### For New Tests

1. **Unit tests**: Place in appropriate component directory
2. **Integration tests**: Name with `test_integration_*.py`
3. **Benchmarks**: Name with `test_*_bench.py`
4. **Test data**: Use existing data directories or fixtures/

### Naming Conventions

- `test_*.py` - Standard test files
- `test_integration_*.py` - Integration tests
- `test_*_bench.py` - Performance benchmarks
- `conftest.py` - pytest configuration

### Shared Test Data

Place reusable test data in:
- `tests/fixtures/` - Cross-component test data (NEW)
- `tests/native/binaries/` - Native binary samples
- `tests/ethereum/contracts/` - Solidity contracts
- `tests/ethereum/data/` - Ethereum test data

## Why This Structure?

1. **Component isolation** - Easy to run tests for specific features
2. **CI/CD friendly** - Tests can be parallelized by component
3. **Preserves history** - Git history and blame remain intact
4. **No breaking changes** - All existing imports continue to work

## Future Improvements (NOT YET)

Potential future reorganization (requires careful migration):
- Split massive generated tests into smaller files
- Create explicit unit/ and integration/ subdirectories
- Extract more shared fixtures

But for now, we maintain stability over perfection.