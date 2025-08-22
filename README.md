# Manticore
<p align="center">
  <img src="https://raw.githubusercontent.com/trailofbits/manticore/master/docs/images/manticore.png" width="256" title="Manticore">
</p>
<br />


[![Build Status](https://img.shields.io/github/actions/workflow/status/trailofbits/manticore/ci.yml?branch=master)](https://github.com/trailofbits/manticore/actions?query=workflow%3ACI)
[![Coverage Status](https://coveralls.io/repos/github/trailofbits/manticore/badge.svg)](https://coveralls.io/github/trailofbits/manticore)
[![PyPI Version](https://badge.fury.io/py/manticore.svg)](https://badge.fury.io/py/manticore)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)



Manticore is a symbolic execution tool for the analysis of smart contracts and binaries.

## Features

- **Program Exploration**: Manticore can execute a program with symbolic inputs and explore all the possible states it can reach
- **Input Generation**: Manticore can automatically produce concrete inputs that result in a given program state
- **Error Discovery**: Manticore can detect crashes and other failure cases in binaries and smart contracts
- **Instrumentation**: Manticore provides fine-grained control of state exploration via event callbacks and instruction hooks
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore can analyze the following types of programs:

- Ethereum smart contracts (EVM bytecode)
- Linux ELF binaries (x86, x86_64, aarch64, and ARMv7)
- WASM Modules

## Platform Support

| Platform | Binary Analysis | Smart Contracts | WASM |
|----------|----------------|-----------------|------|
| Linux x86_64 | ✅ Full | ✅ Full | ✅ Full |
| Linux ARM64 | ✅ Full | ✅ Full* | ✅ Full |
| macOS x86_64 | ⚠️ Limited** | ✅ Full | ✅ Full |
| macOS ARM64 (M1/M2/M3) | ⚠️ Limited** | ✅ Full | ✅ Full |
| Windows | ⚠️ Experimental | ⚠️ Experimental | ⚠️ Experimental |

\* *Requires QEMU for x86_64 Solidity compiler binaries on ARM64*

\*\* *Binary analysis on macOS uses threading instead of multiprocessing, which is slower but more stable*

## Installation

> **Requirements**: Python >= 3.9

### Quick Install with uv (Recommended)

[uv](https://github.com/astral-sh/uv) is a fast Python package and project manager that handles virtual environments automatically:

```bash
# Install uv if you don't have it
curl -LsSf https://astral.sh/uv/install.sh | sh

# Install Manticore with all dependencies for binary analysis
uv pip install --system "manticore[native]"
```

### Developer Installation (Recommended for Contributors)

For development work, we provide automated setup scripts that handle everything:

```bash
git clone https://github.com/trailofbits/manticore.git
cd manticore

# Option 1: Automated setup with uv (recommended)
python scripts/dev_setup.py

# Option 2: Manual setup with uv
uv venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate
uv pip install -e ".[native,dev]"
```

The automated setup script will:
- Install uv if not present
- Create and activate a virtual environment
- Install Manticore in editable mode with all dependencies
- Install pre-commit hooks for code quality
- Detect platform-specific requirements (solc, QEMU, etc.)

### Alternative Installation Methods

<details>
<summary>Using pip (traditional method)</summary>

```bash
# From PyPI
pip install "manticore[native]"

# Development install
git clone https://github.com/trailofbits/manticore.git
cd manticore
pip install -e ".[native,dev]"
```
</details>

<details>
<summary>Using Docker</summary>

```bash
docker pull trailofbits/manticore

# Run with increased stack size
docker run --rm -it --ulimit stack=100000000:100000000 trailofbits/manticore
```
</details>

<details>
<summary>Nightly builds</summary>

```bash
# Install pre-release version
uv pip install --system --pre "manticore[native]"
```
</details>

## Usage

### CLI

Manticore has a command line interface which can perform a basic symbolic analysis of a binary or smart contract. 
Analysis results will be placed into a workspace directory beginning with `mcore_`. For information about the workspace, see the [wiki](https://github.com/trailofbits/manticore/wiki/What's-in-the-workspace%3F).

#### Smart Contracts (EVM)
Manticore CLI automatically detects you are trying to test a contract if (for ex.)
 the contract has a `.sol` or a `.vy` extension. See a [demo](https://asciinema.org/a/154012).
<details>
  <summary>Click to expand:</summary>
  
```bash
$ manticore examples/evm/umd_example.sol 
 [9921] m.main:INFO: Registered plugins: DetectUninitializedMemory, DetectReentrancySimple, DetectExternalCallAndLeak, ...
 [9921] m.e.manticore:INFO: Starting symbolic create contract
 [9921] m.e.manticore:INFO: Starting symbolic transaction: 0
 [9921] m.e.manticore:INFO: 4 alive states, 6 terminated states
 [9921] m.e.manticore:INFO: Starting symbolic transaction: 1
 [9921] m.e.manticore:INFO: 16 alive states, 22 terminated states
[13761] m.c.manticore:INFO: Generated testcase No. 0 - STOP(3 txs)
[13754] m.c.manticore:INFO: Generated testcase No. 1 - STOP(3 txs)
...
[13743] m.c.manticore:INFO: Generated testcase No. 36 - THROW(3 txs)
[13740] m.c.manticore:INFO: Generated testcase No. 37 - THROW(3 txs)
[9921] m.c.manticore:INFO: Results in ~/manticore/mcore_gsncmlgx
```
</details>

##### Manticore-verifier

An alternative CLI tool is provided that simplifies contract testing and 
allows writing properties methods in the same high-level language the contract uses.
Checkout manticore-verifier [documentation](http://manticore.readthedocs.io/en/latest/verifier.html).
See a [demo](https://asciinema.org/a/xd0XYe6EqHCibae0RP6c7sJVE)

#### Native Binaries
<details>
  <summary>Click to expand:</summary>
  
```bash
$ manticore examples/linux/basic
[9507] m.n.manticore:INFO: Loading program examples/linux/basic
[9507] m.c.manticore:INFO: Generated testcase No. 0 - Program finished with exit status: 0
[9507] m.c.manticore:INFO: Generated testcase No. 1 - Program finished with exit status: 0
[9507] m.c.manticore:INFO: Results in ~/manticore/mcore_7u7hgfay
[9507] m.n.manticore:INFO: Total time: 2.8029580116271973
```
</details>


### API

Manticore provides a Python programming interface which can be used to implement powerful custom analyses.

#### Smart Contracts (EVM)
For Ethereum smart contracts, the API can be used for detailed verification of arbitrary contract properties. Users can set the starting conditions, 
execute symbolic transactions, and then review discovered states to ensure invariants for a contract hold.
<details>
  <summary>Click to expand:</summary>
  
```python
from manticore.ethereum import ManticoreEVM
contract_src="""
contract Adder {
    function incremented(uint value) public returns (uint){
        if (value == 1)
            revert();
        return value + 1;
    }
}
"""
m = ManticoreEVM()

user_account = m.create_account(balance=10000000)
contract_account = m.solidity_create_contract(contract_src,
                                              owner=user_account,
                                              balance=0)
value = m.make_symbolic_value()

contract_account.incremented(value)

for state in m.ready_states:
    print("can value be 1? {}".format(state.can_be_true(value == 1)))
    print("can value be 200? {}".format(state.can_be_true(value == 200)))
```
</details>

#### Native Binaries
It is also possible to use the API to create custom analysis tools for Linux binaries. Tailoring the initial state helps avoid state explosion
problems that commonly occur when using the CLI. 

<details>
  <summary>Click to expand:</summary>
  
```python
# example Manticore script
from manticore.native import Manticore

m = Manticore.linux('./example')

@m.hook(0x400ca0)
def hook(state):
  cpu = state.cpu
  print('eax', cpu.EAX)
  print(cpu.read_int(cpu.ESP))

  m.kill()  # tell Manticore to stop

m.run()
```
</details>


#### WASM
Manticore can also evaluate WebAssembly functions over symbolic inputs for property validation or general analysis. 

<details>
  <summary>Click to expand:</summary>
  
```python
from manticore.wasm import ManticoreWASM

m = ManticoreWASM("collatz.wasm")

def arg_gen(state):
    # Generate a symbolic argument to pass to the collatz function.
    # Possible values: 4, 6, 8
    arg = state.new_symbolic_value(32, "collatz_arg")
    state.constrain(arg > 3)
    state.constrain(arg < 9)
    state.constrain(arg % 2 == 0)
    return [arg]


# Run the collatz function with the given argument generator.
m.collatz(arg_gen)

# Manually collect return values
# Prints 2, 3, 8
for idx, val_list in enumerate(m.collect_returns()):
    print("State", idx, "::", val_list[0])
```
</details>

## Examples

Manticore comes with a variety of examples to demonstrate its capabilities:

### Built-in Examples
The [`examples/`](examples/) directory contains simple scripts that showcase various features:
- [`linux/`](examples/linux/): Binary analysis examples
- [`evm/`](examples/evm/): Smart contract examples  
- [`wasm/`](examples/wasm/): WebAssembly examples

### Real-World CTF Challenges
The [`examples/real_world_ctf/`](examples/real_world_ctf/) directory contains solutions to actual CTF challenges:
- Binary exploitation challenges (pwnable, crackmes, etc.)
- Smart contract security challenges
- Automated exploit generation
- See the [CTF examples README](examples/real_world_ctf/README.md) for the full list

### External Repository
For more complex examples, visit the [manticore-examples](https://github.com/trailofbits/manticore-examples) repository.

## Requirements & Dependencies

### Core Requirements
* Python 3.9 or greater
* Increased stack size for symbolic execution:
  - Linux/macOS: `ulimit -s 100000`
  - Docker: `--ulimit stack=100000000:100000000`

### Platform-Specific Notes

#### Linux (Recommended Platform)
- Full support for all features
- Best performance with native multiprocessing

#### macOS
- Binary analysis uses threading (slower than Linux)
- EVM and WASM fully supported
- Install Command Line Tools: `xcode-select --install`

#### Windows
- Experimental support via WSL2 or Docker
- Native Windows support is limited

### Smart Contract Analysis
- Requires [`solc`](https://github.com/ethereum/solidity) in your `$PATH`
- Uses [crytic-compile](https://github.com/crytic/crytic-compile) for compilation
- For compilation issues, try running `crytic-compile` directly

### Optional: Alternative SMT Solvers

Manticore uses Z3 by default but supports other solvers for better performance:

<details>
<summary>Installing Yices (fastest)</summary>

```bash
# Ubuntu
sudo add-apt-repository ppa:sri-csl/formal-methods
sudo apt-get update
sudo apt-get install yices2

# macOS
brew install SRI-CSL/sri-csl/yices2
```
</details>

<details>
<summary>Installing CVC4</summary>

```bash
# Linux
sudo wget -O /usr/bin/cvc4 https://github.com/CVC4/CVC4/releases/download/1.7/cvc4-1.7-x86_64-linux-opt
sudo chmod +x /usr/bin/cvc4

# macOS
brew tap cvc4/cvc4
brew install cvc4
```
</details>

Select solver via: `manticore --smt.solver yices`

## Getting Help

Feel free to stop by our #manticore slack channel in [Empire Hacking](https://slack.empirehacking.nyc/) for help using or extending Manticore.

Documentation is available in several places:

  * The [wiki](https://github.com/trailofbits/manticore/wiki) contains information about getting started with Manticore and contributing

  * The [API reference](http://manticore.readthedocs.io/en/latest/) has more thorough and in-depth documentation on our API
    
  * The [examples](examples) directory has small examples that showcase API features

  * The [manticore-examples](https://github.com/trailofbits/manticore-examples) repository has more involved examples

If you'd like to file a bug report or feature request, please use our [issues](https://github.com/trailofbits/manticore/issues/choose) page. 

For questions and clarifications, please visit the [discussion](https://github.com/trailofbits/manticore/discussions) page.

## License

Manticore is licensed and distributed under the AGPLv3 license. [Contact us](mailto:opensource@trailofbits.com) if you're looking for an exception to the terms.

## Publications
- [Manticore: A User-Friendly Symbolic Execution Framework for Binaries and Smart Contracts](https://arxiv.org/abs/1907.03890), Mark Mossberg, Felipe Manzano, Eric Hennenfent, Alex Groce, Gustavo Grieco, Josselin Feist, Trent Brunson, Artem Dinaburg - ASE 19

If you are using Manticore in academic work, consider applying to the [Crytic $10k Research Prize](https://blog.trailofbits.com/2019/11/13/announcing-the-crytic-10k-research-prize/).

## Demo Video from ASE 2019
[![Brief Manticore demo video](https://img.youtube.com/vi/o6pmBJZpKAc/1.jpg)](https://youtu.be/o6pmBJZpKAc)

## Tool Integrations 

- [MATE: Merged Analysis To prevent Exploits](https://github.com/GaloisInc/MATE)
  * [Mantiserve:](https://galoisinc.github.io/MATE/mantiserve.html) REST API interaction with Manticore to start, kill, and check Manticore instance
  * [Dwarfcore:](https://galoisinc.github.io/MATE/dwarfcore.html) Plugins and detectors for use within Mantiserve engine during exploration 
  * [Under-constrained symbolic execution](https://github.com/GaloisInc/MATE/blob/main/doc/under-constrained-manticore.rst) Interface for symbolically exploring single functions with Manticore