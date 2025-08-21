# Recommended Test Markers

Based on analysis of the test suite, here are the recommended markers for each test file.

## ⚠️ IMPORTANT: Start Small

Don't mark all files at once! Start with the most obvious cases:

### Phase 1: Mark Generated Tests (HIGH PRIORITY)
These massive files are likely auto-generated and should be marked to exclude from certain operations:

```python
# In tests/native/test_x86.py (115,432 lines!)
from tests.markers import generated_test, slow_test

@generated_test
@slow_test
class TestX86(unittest.TestCase):
    ...

# In tests/native/test_cpu_automatic.py (46,468 lines!)
from tests.markers import generated_test, slow_test

@generated_test
@slow_test
class CPUTest(unittest.TestCase):
    ...

# In tests/native/test_aarch64cpu.py (14,082 lines)
from tests.markers import generated_test, slow_test

# In tests/native/test_x86_pcmpxstrx.py (30,124 lines)
from tests.markers import generated_test, slow_test
```

### Phase 2: Mark Obvious Special Cases

```python
# In tests/native/test_integration_native.py
from tests.markers import integration_test

@integration_test
class TestIntegration(unittest.TestCase):
    ...

# In tests/ethereum_bench/test_consensys_benchmark.py
from tests.markers import benchmark

@benchmark
class TestConsensusBenchmark(unittest.TestCase):
    ...
```

### Phase 3: Mark Platform-Specific Tests (Optional)

These tests appear to be Linux-specific:
- `tests/native/test_linux.py` - Obviously Linux-specific
- `tests/native/test_syscalls.py` - System calls are OS-specific
- `tests/native/test_armv7unicorn.py` - Uses Unicorn which may be Linux-only

## Complete Marker Recommendations

| Test File | Lines | Recommended Markers | Priority |
|-----------|-------|---------------------|----------|
| native/test_x86.py | 115,432 | @generated_test, @slow_test | HIGH |
| native/test_cpu_automatic.py | 46,468 | @generated_test, @slow_test | HIGH |
| native/test_x86_pcmpxstrx.py | 30,124 | @generated_test, @slow_test | HIGH |
| native/test_aarch64cpu.py | 14,082 | @generated_test, @slow_test | HIGH |
| native/test_integration_native.py | 358 | @integration_test | HIGH |
| ethereum_bench/test_consensys_benchmark.py | 179 | @benchmark | HIGH |
| native/test_slam_regre.py | 5,303 | @slow_test | MEDIUM |
| native/test_dyn.py | 3,800 | @slow_test | MEDIUM |
| native/test_armv7cpu.py | 2,521 | @slow_test | MEDIUM |
| ethereum/test_general.py | 2,079 | @slow_test | MEDIUM |
| native/test_linux.py | 464 | @linux_only | LOW |
| native/test_syscalls.py | 722 | @linux_only | LOW |

## How to Apply Markers

### Option 1: Manual (Safest)
1. Open one file at a time
2. Add import: `from tests.markers import marker_name`
3. Add decorator before test class: `@marker_name`
4. Run tests for that file: `pytest tests/path/to/file.py`
5. Commit if tests pass

### Option 2: Use Helper Script
```bash
# The add_markers.py script can help, but review changes!
python tests/add_markers.py
git diff tests/  # Review all changes
pytest tests/    # Ensure nothing broke
```

## Benefits Once Marked

```bash
# Skip slow/generated tests for quick feedback
pytest -m "not slow_test and not generated_test"

# Run only unit tests
pytest -m "unit_test"

# Run only integration tests
pytest -m "integration_test"

# Skip platform-specific tests on Mac
pytest -m "not linux_only"
```

## ⚠️ Warning

- DO NOT mark all files at once
- DO NOT mark files you're unsure about
- DO TEST after each file you mark
- DO commit working changes before marking more