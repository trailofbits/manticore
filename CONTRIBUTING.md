# Contributing to Manticore

First, thanks for your interest in contributing to Manticore! We welcome and
appreciate all contributions, including bug reports, feature suggestions,
tutorials/blog posts, and code improvements.

If you're unsure where to start, we recommend our [`easy`](https://github.com/trailofbits/manticore/issues?q=is%3Aissue+is%3Aopen+label%3Aeasy) and [`help wanted`](https://github.com/trailofbits/manticore/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22)
issue labels.

## Bug reports and feature suggestions

Bug reports and feature suggestions can be submitted to our [issue
tracker](https://github.com/trailofbits/manticore/issues). For bug reports,
attaching the binary that caused the bug will help us in debugging and
resolving the issue quickly. If you find a security
vulnerability, do not open an issue; email opensource@trailofbits.com
instead.

## Questions

Questions can be submitted to the [discussion page](https://github.com/trailofbits/manticore/discussions), but you may get a faster
response if you ask in our [chat room](https://slack.empirehacking.nyc/)
(in the #manticore channel).

## Legal
For legal reasons, we require contributors to sign our [Contributor License Agreement](https://cla-assistant.io/trailofbits/manticore).
This will be automatically checked as part of our CI. 

## Code

Manticore uses the pull request contribution model. Please make an account on
Github, fork this repo, and submit code contributions via pull request. For
more documentation, look [here](https://guides.github.com/activities/forking/).

Some pull request guidelines:

- We use [`ruff`](https://docs.astral.sh/ruff/) for both linting and formatting
  to enforce style conventions in Manticore. To ensure your code is properly
  formatted and linted, run `ruff check .` and `ruff format .` in the Manticore
  directory before committing. Ruff is significantly faster than traditional
  Python linters and formatters.
- We use the [`mypy`](https://github.com/python/mypy) static typing tool to
  catch inconsistencies in the code base. At the time of this writing, we
  only check the [manticore](./manticore) directory for inconsistencies and do
  not yet enforce new contributions to include type hints. However, we greatly
  appreciate if you do include/add them in any code that you touch in your PR!
  Though, remember the next guideline if you are adding many type-hints, and
  ask for input on how to organize the addition of a massive amount of type
  hints. Check the CI configuration for the exact version of `mypy`.
- Minimize irrelevant changes (formatting, whitespace, etc) to code that would
  otherwise not be touched by this patch. Save formatting or style corrections
  for a separate pull request that does not make any semantic changes.
- When possible, large changes should be split up into smaller focused pull
  requests.
- Fill out the pull request description with a summary of what your patch does,
  key changes that have been made, and any further points of discussion, if
  applicable.
- Title your pull request with a brief description of what it's changing.
  "Fixes #123" is a good comment to add to the description, but makes for an
  unclear title on its own.

## Development Environment

### Quick Setup

Run the automated setup script:
```bash
python scripts/dev_setup.py
```

This will:
- Check prerequisites (Python 3.9+, solc, z3)
- Create a virtual environment
- Install all dependencies
- Setup pre-commit hooks for automatic formatting
- Optionally setup solc-select for managing Solidity versions

### Manual Setup

```bash
# Install development dependencies
pip install -e ".[dev]"

# Setup pre-commit hooks
pre-commit install
```

### Running Tests

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

### Code Quality

We use several tools to maintain code quality, all configured in `pyproject.toml`:

- **ruff**: Fast Python linter and formatter (replaces flake8 and black)
- **mypy**: Static type checker
- **pytest**: Test framework with markers for test categorization

```bash
# Run linters
ruff check .       # Fast linting
ruff format .      # Format code
mypy .            # Type checking

# Pre-commit will run these automatically before commits
```

### Platform Support

| Platform | Support Level | Notes |
|----------|--------------|-------|
| Linux x86_64 | ✅ Full | All features supported |
| Linux ARM64 | ✅ Full* | Requires QEMU for x86_64 solc binaries |
| macOS x86_64 | ⚠️ Partial | Limited native binary analysis |
| macOS ARM64 | ⚠️ Partial | Limited native binary analysis |
| Windows | ⚠️ Experimental | Basic functionality only |

### Common Issues and Solutions

#### Solidity Version Errors

**Problem**: Tests fail with "No visibility specified" or similar errors.

**Solution**: You likely have a newer Solidity version. Use solc-select:
```bash
pip install solc-select
solc-select install 0.4.24
solc-select use 0.4.24
```

#### macOS Performance

**Problem**: Slow execution on macOS due to threading limitations.

**Solution**: Enable multiprocessing mode:
```bash
manticore --core.mprocessing=multiprocessing your_file
```

#### Z3 Solver Not Found

**Problem**: Tests fail with "No Solver not found" errors.

**Solution**: Install Z3:
```bash
# macOS
brew install z3

# Linux
sudo apt install z3
```

#### ARM64/M1 Mac Issues

**Problem**: Solc binaries don't work on ARM64.

**Solution**: 
1. Use Docker with x86_64 emulation
2. Use a Linux VM (Multipass, UTM, etc.)
3. Use rosetta/QEMU emulation (experimental)

### Docker Testing Environment

For consistent Linux-based testing (recommended for macOS users):

```bash
# Build test image
docker build -t manticore-test -f Dockerfile.test .

# Run tests in Docker
docker run --rm -v $(pwd):/manticore manticore-test pytest tests/

# Interactive shell
docker run --rm -it -v $(pwd):/manticore manticore-test bash
```

### Test Markers

Tests are marked for better organization:

| Marker | Description | Usage |
|--------|-------------|-------|
| `slow` | Tests that take >1 minute | `pytest -m "not slow"` |
| `ethereum` | Ethereum/smart contract tests | `pytest -m ethereum` |
| `native` | Native binary analysis tests | `pytest -m native` |
| `wasm` | WebAssembly tests | `pytest -m wasm` |
| `linux` | Linux-only tests | `pytest -m linux` |

### Development Workflow

1. **Create a branch** for your feature/fix
2. **Run relevant tests** before committing
3. **Pre-commit hooks** will automatically format your code
4. **Run the test suite**: `pytest tests/ -m "not slow"`
5. **Update documentation** if needed

### Tips for Faster Development

- Use `pytest-xdist` for parallel testing: `pytest -n auto`
- Skip slow tests during development: `pytest -m "not slow"`
- Use `pytest --lf` to run only last failed tests
- Use `pytest --timeout=30` to catch hanging tests
- Keep multiple solc versions with solc-select
