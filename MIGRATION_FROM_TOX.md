# Migration from tox.ini

This document outlines how to complete the migration from tox.ini to pyproject.toml.

## Current Status

The `tox.ini` file is still present because:
1. **flake8 configuration**: flake8 doesn't natively support pyproject.toml
2. **Multi-Python version testing**: tox is used to test across Python 3.8-3.12

## Migration Options

### Option 1: Use Flake8-pyproject Plugin

Install `Flake8-pyproject` to enable pyproject.toml support:

```toml
# Add to pyproject.toml
[project.optional-dependencies]
lint = [
    "black~=24.0",
    "mypy~=1.0",
    "flake8>=6.0",
    "Flake8-pyproject>=1.2.0",
]

[tool.flake8]
ignore = ["E265", "E501", "F403", "F405", "E266", "E712", "F841", "E741", "E722", "E731"]
max-line-length = 100
exclude = [".tox", ".*.egg", ".git", "docs/", "examples/", "scripts/", "tests/", "iterpickle.py"]
```

### Option 2: Switch to Ruff (Recommended)

Ruff is a modern, fast linter that replaces flake8 and supports pyproject.toml natively:

```toml
# Add to pyproject.toml
[project.optional-dependencies]
lint = [
    "black~=24.0",
    "mypy~=1.0",
    "ruff>=0.1.0",
]

[tool.ruff]
line-length = 100
ignore = ["E265", "E501", "F403", "F405", "E266", "E712", "F841", "E741", "E722", "E731"]
exclude = [".tox", ".*.egg", ".git", "docs/", "examples/", "scripts/", "tests/", "iterpickle.py"]

[tool.ruff.per-file-ignores]
"__init__.py" = ["F401"]
```

### Option 3: Keep tox.ini for flake8 only

If you prefer to keep using flake8 without plugins, you can:
1. Keep a minimal tox.ini with just flake8 config
2. Move tox testing to GitHub Actions or nox

## Testing Multiple Python Versions

### Option A: Use GitHub Actions Matrix

```yaml
# .github/workflows/test.yml
strategy:
  matrix:
    python-version: ["3.8", "3.9", "3.10", "3.11", "3.12"]
steps:
  - uses: actions/setup-python@v4
    with:
      python-version: ${{ matrix.python-version }}
  - run: pip install -e .[dev]
  - run: pytest -n auto tests
```

### Option B: Use nox (supports pyproject.toml)

```python
# noxfile.py
import nox

@nox.session(python=["3.8", "3.9", "3.10", "3.11", "3.12"])
def tests(session):
    session.install("-e", ".[dev]")
    session.run("pytest", "-n", "auto", "tests")
```

### Option C: Keep tox but document it's temporary

Add to pyproject.toml:
```toml
# Note: tox.ini is kept for multi-version testing.
# To run tests across Python versions: tox
# To run tests for current Python: pytest -n auto tests
```

## Recommendation

1. **Immediate**: Switch to ruff for linting (it's much faster and fully compatible)
2. **Short term**: Use GitHub Actions for multi-version testing (already in place)
3. **Long term**: Remove tox.ini completely

## Commands After Migration

Before:
```bash
tox -e py311  # Test with Python 3.11
tox -e pep8   # Run flake8
```

After:
```bash
pytest -n auto tests  # Run tests
ruff check .         # Lint code
black --check .      # Check formatting
mypy .              # Type check
```