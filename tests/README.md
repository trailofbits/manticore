# Manticore Test Suite

This directory contains the comprehensive test suite for Manticore, organized by component.

**IMPORTANT**: Please DO NOT create new directories in tests/ as we run separate directories in separate test jobs in `.github/workflows/ci.yml`

## Test Organization

```
tests/
├── native/          # Native binary analysis tests (x86, ARM, etc.)
│   ├── binaries/    # Test binaries
│   └── *.py         # Test files (including generated CPU tests)
├── ethereum/        # Smart contract tests
│   ├── contracts/   # Test contracts
│   └── data/        # Test data
├── ethereum_bench/  # Ethereum benchmarks
├── wasm/           # WebAssembly tests
├── other/          # Utility and core functionality tests
└── fixtures/       # Shared test utilities and data
```

## Running Tests

### Quick Testing
```bash
# Skip slow and generated tests for rapid feedback
pytest -m "not slow_test and not generated_test"
```

### Component Testing
```bash
pytest -m ethereum_test    # Ethereum tests only
pytest -m native_test      # Native binary tests only
pytest -m wasm_test        # WebAssembly tests only
```

### Full Test Suite
```bash
pytest tests/              # Run everything (may take a while)
```

## Test Markers

Tests are categorized with pytest markers for better organization:

| Marker | Description | Example Usage |
|--------|-------------|---------------|
| `@generated_test` | Auto-generated tests (200k+ lines) | Skip with `-m "not generated_test"` |
| `@slow_test` | Tests that take significant time | Skip with `-m "not slow_test"` |
| `@integration_test` | Tests involving multiple components | Run with `-m integration_test` |
| `@benchmark` | Performance benchmarks | Run with `-m benchmark` |
| `@linux_only` | Linux-specific tests | Skip on Mac with `-m "not linux_only"` |
| `@ethereum_test` | Ethereum/smart contract tests | Run with `-m ethereum_test` |
| `@native_test` | Native binary analysis tests | Run with `-m native_test` |
| `@wasm_test` | WebAssembly tests | Run with `-m wasm_test` |

## Writing Tests

### Adding New Tests

1. Place tests in the appropriate component directory
2. Use markers to categorize your tests:
```python
from tests.markers import slow_test, native_test

@slow_test
@native_test
class TestMyFeature(unittest.TestCase):
    def test_something(self):
        pass
```

3. Use fixtures for shared test data:
```python
from tests.fixtures import load_binary, ETHEREUM_CONTRACTS

def test_binary():
    binary = load_binary("test_program")
    # ... test code
```

### Generated Tests

The following files contain auto-generated CPU instruction tests and should NOT be manually edited:
- `native/test_x86.py` (115k+ lines)
- `native/test_cpu_automatic.py` (46k+ lines)
- `native/test_x86_pcmpxstrx.py` (30k+ lines)
- `native/test_aarch64cpu.py` (14k+ lines)

These tests are marked with `@generated_test` and can be skipped for faster development cycles.

## Test Data

- **Native binaries**: `tests/native/binaries/`
- **Ethereum contracts**: `tests/ethereum/contracts/`
- **Shared fixtures**: `tests/fixtures/`

Test outputs (mcore_* directories) are automatically ignored by git.