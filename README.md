# Manticore

[![Build Status](https://travis-ci.org/trailofbits/manticore.svg?branch=master)](https://travis-ci.org/trailofbits/manticore)
[![PyPI version](https://badge.fury.io/py/manticore.svg)](https://badge.fury.io/py/manticore)
[![Slack Status](https://empireslacking.herokuapp.com/badge.svg)](https://empireslacking.herokuapp.com)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)
[![Bountysource](https://img.shields.io/bountysource/team/trailofbits/activity.svg)](https://www.bountysource.com/teams/trailofbits)

Manticore is a symbolic execution tool for analysis of binaries and smart contracts.

## Features

- **Input Generation**: Manticore automatically generates inputs that trigger unique code paths
- **Crash Discovery**: Manticore discovers inputs that crash programs via memory safety violations
- **Execution Tracing**: Manticore records an instruction-level trace of execution for each generated input
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore can analyze the following types of programs:

- Linux ELF binaries (x86, x86_64 and ARMv7)
- Ethereum smart contracts (EVM bytecode) ([release announcement](https://github.com/trailofbits/manticore/releases/tag/0.1.6))

## Requirements

Manticore is supported on Linux and requires Python 2.7. Ubuntu 16.04 is strongly recommended.
Ethereum smart contract analysis requires the [`solc`](https://github.com/ethereum/solidity) program in your `$PATH`.

## Quick Start

Install and try Manticore in a few shell commands (see an [asciinema](https://asciinema.org/a/567nko3eh2yzit099s0nq4e8z)):

```
# Install system dependencies
sudo apt-get update && sudo apt-get install python-pip -y

# Install manticore and its dependencies
sudo pip2 install manticore

# Download and build the examples
git clone https://github.com/trailofbits/manticore.git && cd manticore/examples/linux
make

# Use the Manticore CLI
manticore basic
cat mcore_*/*0.stdin | ./basic
cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
cd ../script
python count_instructions.py ../linux/helloworld
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

Once installed, the `manticore` CLI tool and Python API will be available.

For installing a development version of Manticore, see our [wiki](https://github.com/trailofbits/manticore/wiki/Hacking-on-Manticore).

## Usage

### CLI

Manticore has a command line interface which can be used to easily symbolically execute a supported program. Analysis results will be placed into a new directory beginning with `mcore_`. Solidity files must have a .sol extension.


```
$ manticore ./path/to/binary        # runs, and creates a mcore_* directory with analysis results
$ manticore ./path/to/binary ab cd  # use concrete strings "ab", "cd" as program arguments
$ manticore ./path/to/binary ++ ++  # use two symbolic strings of length two as program arguments
$ manticore ./path/to/contract.sol
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
  print 'eax', cpu.EAX
  print cpu.read_int(cpu.ESP)

  m.terminate()  # tell Manticore to stop

m.run()
```

Further documentation is available in several places:

  * The [wiki](https://github.com/trailofbits/manticore/wiki) contains some
    basic information about getting started with manticore and contributing

  * The [examples](examples) directory has some very minimal examples that
    showcase API features

  * The [manticore-examples](https://github.com/trailofbits/manticore-examples)
    repository has some more involved examples, for instance solving real CTF problems

  * The [API reference](http://manticore.readthedocs.io/en/latest/) has more
    thorough and in-depth documentation on our API

Manticore is beta software. It is actively developed and maintained, and users should expect improvements, interface changes, and of course, some bugs.
