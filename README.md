# Manticore

[![Build Status](https://travis-ci.org/trailofbits/manticore.svg?branch=master)](https://travis-ci.org/trailofbits/manticore)
[![Slack Status](https://empireslacking.herokuapp.com/badge.svg)](https://empireslacking.herokuapp.com)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)
[![Bountysource](https://img.shields.io/bountysource/team/trailofbits/activity.svg)](https://www.bountysource.com/teams/trailofbits)

Manticore is a prototyping tool for dynamic binary analysis, with support for symbolic execution, taint analysis, and binary instrumentation.

## Features

- **Input Generation**: Manticore automatically generates inputs that trigger unique code paths
- **Crash Discovery**: Manticore discovers inputs that crash programs via memory safety violations
- **Execution Tracing**: Manticore records an instruction-level trace of execution for each generated input
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore supports binaries of the following formats, operating systems, and
architectures. It has been primarily used on binaries compiled from C and C++.
Examples of practical manticore usage are also [on github](https://github.com/trailofbits/manticore-examples).

- OS/Formats: Linux ELF, Windows Minidump
- Architectures: x86, x86_64, ARMv7 (partial)

## Requirements

Manticore is supported on Linux and requires Python 2.7, pip 7.1.0 or higher, and the [Z3 Theorem Prover](https://github.com/Z3Prover/z3/releases). Ubuntu 16.04 is strongly recommended.

## Quick Start

Install and try Manticore in a few shell commands (see an [asciinema](https://asciinema.org/a/567nko3eh2yzit099s0nq4e8z)):

```
# Install system dependencies
sudo apt-get update && sudo apt-get install z3 python-pip -y
python -m pip install -U pip

# Install manticore and its dependencies
git clone https://github.com/trailofbits/manticore.git && cd manticore
sudo pip install .

# Build the examples
cd examples/linux
make

# Use the Manticore CLI
manticore basic
cat mcore_*/*1.stdin | ./basic
cat mcore_*/*2.stdin | ./basic

# Use the Manticore API
cd ../script
python count_instructions.py ../linux/helloworld
```

## Installation

Make sure that Z3 is installed and available on your `PATH`. On Ubuntu, this is as simple as `sudo apt-get install z3`.

Option 1: Perform a user install (requires `~/.local/bin` in your `PATH`).

```
echo "PATH=\$PATH:~/.local/bin" >> ~/.profile
source ~/.profile
git clone https://github.com/trailofbits/manticore.git && cd manticore
pip install --user .
```

Option 2: Use a virtual environment (requires [virtualenvwrapper](https://virtualenvwrapper.readthedocs.io/en/latest/) or [similar](https://virtualenv.pypa.io/en/stable/)).

```
pip install virtualenvwrapper
echo "source /usr/local/bin/virtualenvwrapper.sh" >> ~/.profile
source ~/.profile
git clone https://github.com/trailofbits/manticore.git && cd manticore
mkvirtualenv manticore
pip install .
```

Option 3: Perform a system install.

```
git clone https://github.com/trailofbits/manticore.git && cd manticore
sudo pip install .
```

Once installed, the `manticore` CLI tool and its Python API will be available.

### For developers

For a dev install that includes dependencies for tests, run:

```
pip install --no-binary keystone-engine -e .[dev]
```

You can run the tests with the commands below:

```
cd manticore
# all tests
nosetests
# just one file
nosetests tests/test_armv7cpu.py
# just one test class
nosetests tests/test_armv7cpu.py:Armv7CpuInstructions
# just one test
nosetests tests/test_armv7cpu.py:Armv7CpuInstructions.test_mov_imm_min
```

## Usage

```
$ manticore ./path/to/binary  # runs, and creates a mcore_* directory with analysis results
```

or

```python
# example Manticore script
from manticore import Manticore

hook_pc = 0x400ca0

m = Manticore('./path/to/binary')

@m.hook(hook_pc)
def hook(state):
  cpu = state.cpu
  print 'eax', cpu.EAX
  print cpu.read_int(cpu.SP)

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

