# Test Fixtures

This directory contains shared test data and utilities that can be used across multiple test files.

## Usage

```python
from pathlib import Path

# Get path to fixtures directory
FIXTURES_DIR = Path(__file__).parent.parent / "fixtures"

# Load a fixture file
fixture_path = FIXTURES_DIR / "sample_data.json"
```

## What Goes Here?

- Shared test data files (JSON, YAML, etc.)
- Common test utilities (helpers.py)
- Mock objects used by multiple tests
- Sample contracts/binaries for testing

## What DOESN'T Go Here?

- Component-specific test data (use component directories)
- Large binary files (use git-lfs or external storage)
- Generated test files
- Actual test files (test_*.py)

## Current Fixtures

- `common_contracts.py` - Commonly used Solidity contract snippets (TODO)
- `test_helpers.py` - Shared test utility functions (TODO)