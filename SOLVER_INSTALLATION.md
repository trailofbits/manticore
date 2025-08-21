# SMT Solver Installation Guide

Manticore uses SMT solvers for symbolic execution. While Z3 is installed by default via pip, other solvers can improve performance and reliability.

## Current Issues with CI Solver Installation

1. **CVC4 is deprecated** - The project moved to cvc5, but Manticore still uses CVC4
2. **Boolector builds from source** - Time-consuming and fragile
3. **Yices installation varies** - Different methods across workflows

## Recommended Solver Setup

### For Local Development

```bash
# Z3 (installed automatically with manticore)
pip install z3-solver

# Yices (macOS)
brew install SRI-CSL/sri-csl/yices2

# Yices (Ubuntu/Debian)
sudo add-apt-repository ppa:sri-csl/formal-methods
sudo apt-get update
sudo apt-get install yices2

# CVC4 (still used, not cvc5 yet)
# Download the binary for your platform from:
# https://github.com/CVC4/CVC4/releases/tag/1.7
```

### For Docker

The Docker setup includes Z3 by default. Additional solvers can be installed but are optional.

## Solver Configuration

Use the solver configuration script:
```bash
python scripts/configure_solver.py
```

Or manually create `.manticore.yml`:
```yaml
smt:
  solver: z3  # or yices, cvc4, boolector, portfolio
```

## Future Improvements Needed

1. **Migrate to cvc5** - Requires code changes to support new API
2. **Provide pre-built solver binaries** - Avoid building from source
3. **Containerize solver installation** - Use Docker images with pre-installed solvers
4. **Make solvers truly optional** - Ensure tests pass with just Z3

## Why We're Not Upgrading Yet

- **CVC4 → cvc5**: API changes would require significant code updates
- **Boolector**: No longer maintained, but still works
- **Stable is better**: Current solver versions work, major upgrades risk breaking changes

## Testing with Different Solvers

```bash
# Test with Z3 (default)
pytest tests/

# Test with specific solver
MANTICORE_SOLVER=yices pytest tests/

# Test with portfolio (uses all available)
MANTICORE_SOLVER=portfolio pytest tests/
```