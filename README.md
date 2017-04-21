# Manticore

[![Build Status](https://travis-ci.com/trailofbits/manticore.svg?token=m4YsYkGcyttTxRXGVHMr&branch=master)](https://travis-ci.com/trailofbits/manticore)
[![Slack Status](https://empireslacking.herokuapp.com/badge.svg)](https://empireslacking.herokuapp.com)

Manticore is a prototyping tool for dynamic binary analysis, with support for [symbolic execution](https://gist.github.com/ehennenfent/a5ad9746615d1490c618a88b98769c10#file-2multiple_styles_symbolic_solve-py), [taint analysis](/examples/script/introduce_symbolic_bytes.py), and [binary instrumentation](https://gist.github.com/ehennenfent/a5ad9746615d1490c618a88b98769c10#file-1multiple_styles_concrete_solve-py).

## Features

- **Input Generation**: Manticore automatically generates inputs that trigger unique code paths
- **Crash Discovery**: Manticore discovers inputs that crash programs via memory safety violations
- **Execution Tracing**: Manticore records an instruction-level trace of execution for each generated input
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore supports binaries of the following formats, operating systems, and
architectures. It has been primarily used on binaries compiled from C and C++.

- OS/Formats: Linux ELF, Windows Minidump
- Architectures: x86, x86_64, ARMv7 (partial)

## Requirements

Manticore is supported on Linux and requires Python 2.7, pip 7.1.0, and Z3.

## Quick Start

Install and try Manticore in a few shell commands:

```
# Install system dependency
sudo apt-get install z3

# Install manticore and python dependencies
git clone https://github.com/trailofbits/manticore.git
cd manticore
pip install --user --upgrade --no-binary capstone .

# Some example usage
cd examples/linux
make
manticore basic
cat mcore_*/*1.stdin | ./basic
cat mcore_*/*2.stdin | ./basic
cd ../script
python count_instructions.py ../linux/helloworld # ok if the insn count is different
```

Here's an asciinema of what it should look like: https://asciinema.org/a/567nko3eh2yzit099s0nq4e8z

## Installation

Make sure that Z3 Theorem Prover is installed and available on your path. On Ubuntu, this is as simple as `sudo apt-get install z3`.
Then download the Manticore source, and `cd` to the project root.

Option 1: Perform a user install.

```
pip install --user --no-binary capstone .
```

Option 2: Use a [virtual environment](https://virtualenvwrapper.readthedocs.io/en/latest/).

```
mkvirtualenv manticore
pip install --no-binary capstone .
```

Once installed via either method, the `manticore` CLI tool and its Python API will be available.

### For developers

For a dev install that includes dependencies for tests, run:

```
pip install --no-binary capstone --no-binary keystone-engine -e .[dev]
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

- [Multiple Styles: The Writeup](https://gist.github.com/ehennenfent/a5ad9746615d1490c618a88b98769c10)

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
