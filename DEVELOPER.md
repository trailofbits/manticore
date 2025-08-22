# Developer Guide

This guide helps developers get started with Manticore development.

## Quick Start

Run the automated setup script:
```bash
python scripts/dev_setup.py
```

This will:
- Check prerequisites (Python 3.9+, solc, z3)
- Create a virtual environment
- Install all dependencies
- Optionally setup solc-select for managing Solidity versions

## Platform Support

| Platform | Support Level | Notes |
|----------|--------------|-------|
| Linux x86_64 | ✅ Full | All features supported |
| Linux ARM64 | ✅ Full* | Requires QEMU for x86_64 solc binaries |
| macOS x86_64 | ⚠️ Partial | Limited native binary analysis |
| macOS ARM64 | ⚠️ Partial | Limited native binary analysis |
| Windows | ⚠️ Experimental | Basic functionality only |

## Running Tests

```bash
# Activate virtual environment
source .venv/bin/activate

# Run all tests
pytest tests/

# Skip slow tests (recommended for development)
pytest tests/ -m "not slow"

# Run specific test suites
pytest tests/ethereum/      # Ethereum/smart contract tests
pytest tests/native/        # Native binary tests
pytest tests/wasm/          # WebAssembly tests

# Run with timeout to catch hanging tests
pytest tests/ --timeout=30

# Run in parallel for speed
pytest tests/ -n auto
```

## Common Issues and Solutions

### Solidity Version Errors

**Problem**: Tests fail with "No visibility specified" or similar errors.

**Solution**: You likely have a newer Solidity version. Use solc-select:
```bash
pip install solc-select
solc-select install 0.4.24
solc-select use 0.4.24
```

### macOS Warnings

**Problem**: Constant "Manticore is only supported on Linux" warnings.

**Solution**: These are now reduced to a single info message per session after our improvements.

### Z3 Solver Not Found

**Problem**: Tests fail with "No Solver not found" errors.

**Solution**: Install Z3:
```bash
# macOS
brew install z3

# Linux
sudo apt install z3
```

### ARM64/M1 Mac Issues

**Problem**: Solc binaries don't work on ARM64.

**Solution**: 
1. Use Docker with x86_64 emulation
2. Use a Linux VM (Multipass, UTM, etc.)
3. Use rosetta/QEMU emulation (experimental)

## Test Markers

Tests are marked for better organization:

| Marker | Description | Usage |
|--------|-------------|-------|
| `slow` | Tests that take >1 minute | `pytest -m "not slow"` |
| `ethereum` | Ethereum/smart contract tests | `pytest -m ethereum` |
| `native` | Native binary analysis tests | `pytest -m native` |
| `wasm` | WebAssembly tests | `pytest -m wasm` |
| `linux` | Linux-only tests | `pytest -m linux` |

## Development Workflow

1. **Create a branch** for your feature/fix
2. **Run relevant tests** before committing
3. **Use ruff** for formatting: `ruff format .`
4. **Check with mypy**: `mypy manticore/`
5. **Run the test suite**: `pytest tests/ -m "not slow"`
6. **Update documentation** if needed

## Tips for Faster Development

- Use `pytest-xdist` for parallel testing: `pytest -n auto`
- Skip slow tests during development: `pytest -m "not slow"`
- Use `pytest --lf` to run only last failed tests
- Use `pytest --timeout=30` to catch hanging tests
- Keep multiple solc versions with solc-select

## Contributing

1. Fork the repository
2. Create your feature branch
3. Make your changes
4. Run tests
5. Submit a pull request

See [CONTRIBUTING.md](CONTRIBUTING.md) for detailed guidelines.