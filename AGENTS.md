# Agent Quickstart (Manticore)

- Install deps: `uv pip install -e .[dev-noks]` (native: `.[dev]`)
- Lint: `ruff check .` | Fix: `ruff check --fix .`
- Format: `ruff format .`
- Types: `mypy` (strict on public APIs)
- Tests (all): `pytest --durations=10 -n auto`
- Tests (fast): `pytest -xvs -m "not slow and not generated" --no-cov -n auto`
- Test marker groups: `pytest -m "ethereum"` | `-m "native"` | `-m "wasm"`
- Single test: `pytest tests/path/to/test.py::TestClass::test_method -q`
- Server: `cd server && just init && just test` (lint/build: `just lint` | `just build`)
- Pre-commit: `pre-commit install` · run all: `pre-commit run --all-files`

Style (Python):
- 100-char lines; double quotes; ≤50 lines/function; cyclomatic complexity ≤8
- ≤5 positional params; ≤6 returns; ≤12 branches; no relative imports
- Google-style docstrings on all public symbols; complete type hints
- Import order: stdlib, third-party, local (absolute only)
- Naming: Classes PascalCase; funcs/vars snake_case; CONSTS UPPER_SNAKE; private _prefix
- Errors: raise specific exceptions; validate inputs; no bare `except:`; use `manticore.exceptions`

Testing:
- Tests live in `tests/`; mirror source; use pytest markers; descriptive names

Notes:
- No Cursor/Copilot rule files detected
- Do not commit secrets; prefer safe serialization; least privilege
