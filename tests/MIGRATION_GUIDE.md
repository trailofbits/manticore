# Test Organization Migration Guide

## ⚠️ IMPORTANT: This is Optional

The current test structure works fine. These improvements are optional and can be adopted gradually.

## Safe Changes You Can Make Now

### 1. Use Test Markers (No Breaking Changes)

Add markers to existing tests to categorize them:

```python
# In test_integration_native.py
from tests.markers import integration_test, slow_test

@integration_test
@slow_test
class TestIntegration(unittest.TestCase):
    def test_something(self):
        pass
```

Then run specific categories:
```bash
# Run only fast tests
pytest -m "not slow"

# Run only integration tests  
pytest -m integration

# Run unit tests only
pytest -m "unit and not integration"
```

### 2. Use Shared Fixtures (New Tests Only)

For NEW tests, use the fixtures directory:

```python
from tests.fixtures import ETHEREUM_CONTRACTS, load_binary

def test_new_feature():
    # Use shared test data
    binary = load_binary("test_binary")
    contract_path = ETHEREUM_CONTRACTS / "test.sol"
```

### 3. Document Test Types

Add a comment at the top of test files:

```python
"""
Unit tests for X86 CPU instructions.

Test Type: Unit
Component: Native
Generated: No
"""
```

## What NOT to Do

### ❌ DON'T Move These Files:
- `test_x86.py` (115k lines - generated)
- `test_cpu_automatic.py` (46k lines - generated)
- Any file referenced in CI workflows

### ❌ DON'T Rename Existing Tests
- Breaks git history
- Breaks imports
- Breaks CI

### ❌ DON'T Change Directory Structure
- Current structure matches Manticore's architecture
- CI depends on current paths

## Future Improvements (Requires Planning)

If we ever do a major refactoring:

1. **Split generated tests** - Break 100k+ line files into smaller chunks
2. **Create subdirectories** - unit/, integration/, benchmarks/
3. **Extract common code** - Move duplicated test utilities to fixtures/

But this requires:
- Updating all CI workflows
- Fixing all imports
- Extensive testing
- Team consensus

## Summary

✅ **Safe Now**: Add markers, use fixtures for new tests, document
❌ **Don't Touch**: Generated tests, existing structure, file names
🔮 **Maybe Later**: Major reorganization (needs careful planning)