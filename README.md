# Manticore

[![Build Status](https://travis-ci.org/trailofbits/manticore.svg?branch=master)](https://travis-ci.org/trailofbits/manticore)
[![PyPI version](https://badge.fury.io/py/manticore.svg)](https://badge.fury.io/py/manticore)
[![Slack Status](https://empireslacking.herokuapp.com/badge.svg)](https://empireslacking.herokuapp.com)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)
[![Maintainability](https://api.codeclimate.com/v1/badges/9161568d8378cea903f4/maintainability)](https://codeclimate.com/github/trailofbits/manticore/maintainability)
[![Test Coverage](https://api.codeclimate.com/v1/badges/9161568d8378cea903f4/test_coverage)](https://codeclimate.com/github/trailofbits/manticore/test_coverage)

Manticore is a symbolic execution tool for analysis of binaries and smart contracts.

> Note: Beginning with version 0.2.0, Python 3.6+ is required.

## Features

- **Input Generation**: Manticore automatically generates inputs that trigger unique code paths
- **Crash Discovery**: Manticore discovers inputs that crash programs via memory safety violations
- **Execution Tracing**: Manticore records an instruction-level trace of execution for each generated input
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore can analyze the following types of programs:

- Linux ELF binaries (x86, x86_64 and ARMv7)
- Ethereum smart contracts (EVM bytecode)

## Usage

### CLI

Manticore has a command line interface which can be used to easily symbolically execute a supported program. Analysis results will be placed into a new directory beginning with `mcore_`.

```
$ manticore ./path/to/binary        # runs, and creates a mcore_* directory with analysis results
$ manticore ./path/to/binary ab cd  # use concrete strings "ab", "cd" as program arguments
$ manticore ./path/to/binary ++ ++  # use two symbolic strings of length two as program arguments
```

### API

Manticore has a Python programming interface which can be used to implement custom analyses.

```python
# example Manticore script
from manticore import Manticore

hook_pc = 0x400ca0

m = Manticore('./path/to/binary')

@m.hook(hook_pc)
def hook(state):
  cpu = state.cpu
  print('eax', cpu.EAX)
  print(cpu.read_int(cpu.ESP))

  m.terminate()  # tell Manticore to stop

m.run()
```

### Ethereum

Manticore includes a symbolic Ethereum Virtual Machine (EVM) and a convenient interface for automated compilation and analysis of Solidity. It integrates with [Ethersplay](https://github.com/trailofbits/ethersplay), Trail of Bits’ visual disassembler for EVM bytecode, for analysis visualization. As with binaries, Manticore offers a simple command line interface and a Python API for analysis of EVM bytecode.

Use the CLI to explore possible states in Ethereum smart contracts. Manticore includes _detectors_ which flag certain conditions, including known vulnerable code, as it explores possible states. Solidity smart contracts must have a `.sol` extension for analysis by Manticore. See a demo: https://asciinema.org/a/154012

```
$ manticore ./path/to/contract.sol  # runs, and creates a mcore_* directory with analysis results
$ manticore --detect-reentrancy ./path/to/contract.sol  # Above, but with reentrancy detection enabled
$ manticore --detect-all ./path/to/contract.sol  # Above, but with all detectors enabled
```

Manticore is capable of detailed verification of arbitrary properties of smart contracts via its Python API. Set starting conditions, identify symbolic transactions, then review discovered states to ensure invariants for your contract hold.

```python
from manticore.ethereum import ManticoreEVM
contract_src="""
contract Contract {
    function foo(uint value) public returns (uint){
        if(value==1) revert();
        return value+1;
    }
}
"""
m = ManticoreEVM()

user_account=m.create_account(balance=1000)
contract_account=m.solidity_create_contract(contract_src,
                                            owner=user_account,
                                            balance=0)
bar=m.make_symbolic_value()

contract_account.foo(bar)

for state in m.running_states:
    print("can bar be 1? {}".format(state.can_be_true(bar==1)))
    print("can bar be 200? {}".format(state.can_be_true(bar==200)))

```

## Requirements

* Manticore is supported on Linux and requires **Python 3.6+**.
* Ubuntu 18.04 is strongly recommended.
* Ethereum smart contract analysis requires the [`solc`](https://github.com/ethereum/solidity) program in your `$PATH`.

## Quickstart

Install and try Manticore in a few shell commands (see an [asciinema](https://asciinema.org/a/567nko3eh2yzit099s0nq4e8z)):

```
# Install system dependencies
sudo apt-get update && sudo apt-get install python3 python-pip3 -y

# Install manticore and its dependencies
sudo pip3 install manticore

# Download the examples
git clone https://github.com/trailofbits/manticore.git && cd manticore/examples/linux

# Build the examples
make

# Use the Manticore CLI
manticore basic
cat mcore_*/*0.stdin | ./basic
cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
cd ../script
python3 count_instructions.py ../linux/helloworld
```

You can also use Docker to quickly install and try Manticore:

```
# Download manticore image
docker pull trailofbits/manticore

# Download the examples
git clone https://github.com/trailofbits/manticore.git && cd manticore

# Run container with a shared examples/ directory
docker run -it -v $PWD/examples:/home/manticore/examples trailofbits/manticore

# Change to examples directory
manticore@80d441275ebf$ cd examples/linux

# Build the examples
manticore@80d441275ebf$ make

# Use the Manticore CLI
manticore@80d441275ebf$ manticore basic
manticore@80d441275ebf$ cat mcore_*/*0.stdin | ./basic
manticore@80d441275ebf$ cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
manticore@80d441275ebf$ cd ../script
manticore@80d441275ebf$ python3 count_instructions.py ../linux/helloworld
```

## Installation

Option 1: Perform a user install (requires `~/.local/bin` in your `PATH`).

```
echo "PATH=\$PATH:~/.local/bin" >> ~/.profile
source ~/.profile
pip install --user manticore
```

Option 2: Use a virtual environment (requires [virtualenvwrapper](https://virtualenvwrapper.readthedocs.io/en/latest/) or [similar](https://virtualenv.pypa.io/en/stable/)).

```
pip install virtualenvwrapper
echo "source /usr/local/bin/virtualenvwrapper.sh" >> ~/.profile
source ~/.profile
mkvirtualenv manticore
pip install manticore
```

Option 3: Perform a system install.

```
sudo pip install manticore
```

Option 4: Install via Docker.

```
docker pull trailofbits/manticore
```

Once installed, the `manticore` CLI tool and Python API will be available.

For installing a development version of Manticore, see our [wiki](https://github.com/trailofbits/manticore/wiki/Hacking-on-Manticore).

## Documentation

Documentation is available in several places:

  * The [wiki](https://github.com/trailofbits/manticore/wiki) contains some
    basic information about getting started with manticore and contributing

  * The [examples](examples) directory has some very minimal examples that
    showcase API features

  * The [API reference](http://manticore.readthedocs.io/en/latest/) has more
    thorough and in-depth documentation on our API

  * The [manticore-examples](https://github.com/trailofbits/manticore-examples)
    repository has some more involved examples, for instance solving real CTF problems
