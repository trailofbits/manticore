# Running Manticore Tests in Docker

This document explains how to run Manticore tests in a Linux Docker container, which is useful for macOS users or when you need a consistent test environment.

## Quick Start

```bash
# Run all tests with default solver (z3)
./run-tests-docker.sh

# Run Ethereum tests only
./run-tests-docker.sh ethereum

# Run native tests only
./run-tests-docker.sh native

# Run specific test file
./run-tests-docker.sh tests/ethereum/test_general.py

# Start interactive bash session in container
./run-tests-docker.sh bash

# Check available solvers
./run-tests-docker.sh check-solvers
```

## Solver Configuration

The Docker image supports configurable SMT solvers. By default, it uses Z3, but you can configure it to use other solvers.

### Available Solvers

- **z3** - Z3 theorem prover (installed by default)
- **yices** - Yices2 SMT solver (available for x86_64 only)
- **auto** - Automatically detect and use first available solver

### Setting the Solver

You can specify which solver to use via the `MANTICORE_SOLVER` environment variable:

```bash
# Use Z3 explicitly
MANTICORE_SOLVER=z3 ./run-tests-docker.sh

# Use Yices (if available)
MANTICORE_SOLVER=yices ./run-tests-docker.sh

# Auto-detect (uses first available: yices, then z3)
MANTICORE_SOLVER=auto ./run-tests-docker.sh
```

### Checking Solver Configuration

To see which solvers are available in the container:

```bash
./run-tests-docker.sh check-solvers
```

### Manual Configuration in Container

If you start an interactive bash session, you can manually configure the solver:

```bash
# Start bash session
./run-tests-docker.sh bash

# Inside container, check available solvers
python scripts/configure_solver.py --check

# Configure to use z3
python scripts/configure_solver.py --solver z3

# Run tests
python -m pytest tests/ethereum/
```

## Architecture Notes

- **x86_64**: Full support for both Z3 and Yices2
- **ARM64/Apple Silicon**: Only Z3 is available (Yices2 doesn't provide ARM64 Linux binaries)

## Docker Image Details

The test Docker image (`Dockerfile.test`) includes:

- Python 3.11
- All Manticore dependencies
- Z3 SMT solver
- Yices2 SMT solver (x86_64 only)
- Build tools for native extensions

## Troubleshooting

### Tests fail with "No Solver not found"

This means the SMT solver isn't properly configured. Try:

1. Check available solvers: `./run-tests-docker.sh check-solvers`
2. Explicitly set Z3: `MANTICORE_SOLVER=z3 ./run-tests-docker.sh`
3. Rebuild the image: `docker build -f Dockerfile.test -t manticore-test .`

### Docker connection issues

If you're using Colima on macOS and see connection errors:

```bash
# Restart Colima
colima stop
colima start -m 8  # Start with 8GB memory

# Then retry
./run-tests-docker.sh
```

### Solidity compilation tests fail

Some tests require a Solidity compiler. The Docker image doesn't include solc by default to avoid architecture compatibility issues. Tests that require actual Solidity compilation will be skipped.

## Implementation Notes

The solver configuration works by:

1. Creating a `.manticore.yml` config file in the container
2. Setting the `smt.solver` configuration option
3. The test file `tests/ethereum/test_general.py` has been modified to respect this configuration instead of hardcoding PortfolioSolver

The configuration script (`scripts/configure_solver.py`) handles solver detection and configuration file generation.