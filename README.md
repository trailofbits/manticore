# Manticore

[![Build Status](https://img.shields.io/github/actions/workflow/status/trailofbits/manticore/ci.yml?branch=master)](https://github.com/trailofbits/manticore/actions?query=workflow%3ACI)
[![Coverage Status](https://coveralls.io/repos/github/trailofbits/manticore/badge.svg)](https://coveralls.io/github/trailofbits/manticore)
[![PyPI Version](https://badge.fury.io/py/manticore.svg)](https://badge.fury.io/py/manticore)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)

<p align="center">
  <img src="https://raw.githubusercontent.com/trailofbits/manticore/master/docs/images/manticore.png" width="256" title="Manticore">
</p>

Manticore is a symbolic execution tool for analysis of smart contracts and binaries.

## What is Manticore?

Manticore uses symbolic execution to explore all possible states of a program and automatically generate inputs that trigger unique code paths. It can analyze:

- **Ethereum smart contracts** (EVM bytecode)
- **Linux binaries** (x86, x86_64, aarch64, ARMv7)  
- **WebAssembly modules**

### Key Features

- **Program Exploration**: Discover all reachable states with symbolic inputs
- **Input Generation**: Automatically produce inputs for specific program states
- **Error Discovery**: Detect crashes and failure cases
- **Fine-grained Control**: Use hooks and callbacks to customize analysis

## Quick Start

### 1. Install Manticore

```bash
# Install uv (Python package manager)
curl -LsSf https://astral.sh/uv/install.sh | sh

# Install Manticore
uv pip install --system "manticore[native]"
```

### 2. Analyze a Program

**Smart Contract:**
```bash
$ manticore example.sol
# Analyzes for vulnerabilities like reentrancy, uninitialized memory, integer overflow
```

**Linux Binary:**
```bash
$ manticore ./binary
# Explores execution paths and generates test cases
```

**Python Script:**
```python
from manticore.native import Manticore

m = Manticore.linux('./program')
m.run()
# Results in mcore_* directory
```

### 3. Check Results

Results are saved in a `mcore_*` workspace directory with:
- Test cases that reach different program states
- Inputs that trigger crashes or vulnerabilities
- Execution traces and coverage information

## Installation Options

### Quick Install (Recommended)

Using [uv](https://github.com/astral-sh/uv) (fast, modern Python package manager):

```bash
# Install uv
curl -LsSf https://astral.sh/uv/install.sh | sh

# Install Manticore with binary analysis support
uv pip install --system "manticore[native]"
```

### Docker

```bash
docker pull trailofbits/manticore
docker run --rm -it --ulimit stack=100000000:100000000 trailofbits/manticore
```

### Developer Setup

For contributing to Manticore:

```bash
git clone https://github.com/trailofbits/manticore.git
cd manticore
python scripts/dev_setup.py  # Automated setup with uv
```

The setup script handles:
- Virtual environment creation
- Development dependencies
- Pre-commit hooks
- Platform-specific requirements (solc, QEMU, etc.)

### Other Options

- **pip**: `pip install "manticore[native]"`
- **From source**: `pip install -e ".[native,dev]"`

## Examples & Documentation

### Learn by Example

- **[Built-in Examples](examples/)**: Simple scripts demonstrating core features
  - [Binary analysis](examples/linux/) - Linux ELF analysis
  - [Smart contracts](examples/evm/) - Ethereum contract analysis  
  - [WebAssembly](examples/wasm/) - WASM module analysis

- **[Real CTF Solutions](examples/ctf/)**: Actual security challenges solved with Manticore
  - pwnable challenges
  - Smart contract exploits
  - Automated vulnerability discovery

- **[External Examples](https://github.com/trailofbits/manticore-examples)**: More complex real-world usage

### Documentation

- **[API Reference](http://manticore.readthedocs.io/en/latest/)** - Complete API documentation
- **[Wiki](https://github.com/trailofbits/manticore/wiki)** - Tutorials and guides
- **[Blog Posts](https://blog.trailofbits.com/tag/manticore/)** - Technical deep-dives

### Using the API

Manticore's Python API provides fine-grained control over symbolic execution:

```python
from manticore.native import Manticore

# Hook a specific address
m = Manticore.linux('./binary')

@m.hook(0x400ca0)
def hook(state):
    print(f"Hit address 0x400ca0")
    # Modify state, add constraints, etc.

m.run()
```

For smart contracts:

```python
from manticore.ethereum import ManticoreEVM

m = ManticoreEVM()
contract = m.solidity_create_contract(source_code)
# Explore transactions symbolically
```

## Platform Support & Requirements

### Platform Compatibility

| Platform | Binary Analysis | Smart Contracts | WASM |
|----------|----------------|-----------------|------|
| **Linux x86_64** | ✅ Full | ✅ Full | ✅ Full |
| **Linux ARM64** | ✅ Full | ✅ Full* | ✅ Full |
| **macOS x86_64** | ⚠️ Limited** | ✅ Full | ✅ Full |
| **macOS ARM64** | ⚠️ Limited** | ✅ Full | ✅ Full |
| **Windows** | ⚠️ WSL2/Docker | ⚠️ WSL2/Docker | ⚠️ WSL2/Docker |

\* *Requires QEMU for x86_64 solc on ARM64*  
\*\* *macOS binary analysis uses threading (slower than Linux multiprocessing)*

### System Requirements

- **Python**: 3.9 or greater
- **Memory**: 8GB RAM minimum (16GB+ recommended)
- **Stack Size**: Increase for symbolic execution
  - Linux/macOS: `ulimit -s 100000`
  - Docker: `--ulimit stack=100000000:100000000`

### Additional Dependencies

**For Smart Contract Analysis:**
- `solc` (Solidity compiler) in PATH
- Or use [crytic-compile](https://github.com/crytic/crytic-compile) for automatic compilation

**For macOS:**
- Install Xcode Command Line Tools: `xcode-select --install`

**Optional SMT Solvers** (for better performance):
- **Yices** (fastest): `brew install SRI-CSL/sri-csl/yices2`
- **CVC4**: `brew install cvc4/cvc4/cvc4`
- **Z3**: Included by default

## Getting Help

### Community

- **Chat**: [#manticore on Empire Hacking Slack](https://slack.empirehacking.nyc/)
- **Q&A**: [GitHub Discussions](https://github.com/trailofbits/manticore/discussions)
- **Bugs**: [GitHub Issues](https://github.com/trailofbits/manticore/issues)

### Commercial Support

- [Trail of Bits](https://www.trailofbits.com/contact) offers consulting and training
- Custom feature development available

## Learn More

### Publications & Talks

- [Manticore: Symbolic Execution for Humans](https://blog.trailofbits.com/2017/04/27/manticore-symbolic-execution-for-humans/) - Introductory blog post
- [Academic Paper (ASE 2019)](https://arxiv.org/abs/1907.03890) - Formal presentation
- [Demo Video](https://youtu.be/o6pmBJZpKAc) - Tool demonstration

### Integrations

- **[manticore-verifier](http://manticore.readthedocs.io/en/latest/verifier.html)** - Property-based testing for smart contracts
- **[MATE](https://github.com/GaloisInc/MATE)** - Binary analysis platform integration
  - [MantiServe](https://galoisinc.github.io/MATE/mantiserve.html) - REST API for running Manticore analyses
  - [DwarfCore](https://galoisinc.github.io/MATE/dwarfcore.html) - Enhanced program exploration using DWARF debug info
  - [Under-constrained Manticore](https://github.com/GaloisInc/MATE/blob/main/doc/under-constrained-manticore.rst) - Analyze individual functions without full program context

### Research

Using Manticore in academic work? Consider applying for the [Crytic $10k Research Prize](https://blog.trailofbits.com/2019/11/13/announcing-the-crytic-10k-research-prize/).

## License

Manticore is licensed under AGPLv3. [Contact us](mailto:opensource@trailofbits.com) for commercial licensing options.