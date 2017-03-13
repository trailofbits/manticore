# Manticore

[![Build Status](https://travis-ci.com/trailofbits/manticore.svg?token=m4YsYkGcyttTxRXGVHMr&branch=master)](https://travis-ci.com/trailofbits/manticore)

Manticore is a prototyping tool for dynamic binary analysis, with support for symbolic execution, taint analysis, and binary instrumentation.

## Features

- **Input Generation**: Manticore automatically generates inputs that trigger unique code paths
- **Crash Discovery**: Manticore discovers inputs that crash programs via memory safety violations
- **Execution Tracing**: Manticore records an instruction-level trace of execution for each generated input
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

## Scope

Manticore supports binaries of the following formats, operating systems, and
architectures. It has been primarily used on binaries compiled from C and C++.

- OS/Formats: Linux ELF, Windows Minidump
- Architectures: x86, x86_64, ARMv7 (partial)

## Requirements

Manticore is officially supported on Linux and uses Python 2.7.

## Installation

From the root of the Manticore repository, run:

```
pip install .
````

or, if you would like to do a user install:

```
pip install --user .
```

This installs the Manticore CLI tool `manticore` and the Python API.

Then, install the Z3 Theorem Prover. Download the [latest release](https://github.com/Z3Prover/z3/releases/latest) for your platform and place the `z3` binary in your `$PATH`.

> Note: Due to a known [issue](https://github.com/aquynh/capstone/issues/445),
  Capstone may not install correctly. If you get this error message,
  "ImportError: ERROR: fail to load the dynamic library.", or another related
  to Capstone, try reinstalling via `pip install -I --no-binary capstone capstone`

### For developers

For a dev install, run:

```
pip install -e .[dev]
```

This installs a few other dependencies used for tests which you can run with some of the commands below:

```
cd /path/to/manticore/
# all tests
nosetests
# just one file
nosetests tests/test_armv7cpu.py
# just one test class
nosetests tests/test_armv7cpu.py:Armv7CpuInstructions
# just one test
nosetests tests/test_armv7cpu.py:Armv7CpuInstructions.test_mov_imm_min
```

## Quick start

Install and try Manticore in about ten shell commands:

```
# install z3 before beginning, see our README.md
git clone git@github.com:trailofbits/manticore.git
cd manticore
pip install --user --no-binary capstone . # do this in a virtualenv if you want, but omit --user
cd examples/linux
make
manticore basic
cat mcore_*/*1.stdin | ./basic
cat mcore_*/*2.stdin | ./basic
cd ../script
python count_instructions.py ../linux/helloworld # ok if the insn count is different
```

Here's an asciinema of what it should look like: https://asciinema.org/a/567nko3eh2yzit099s0nq4e8z

## Usage

```
$ manticore ./path/to/binary  # runs, and creates a directory with analysis results
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

## FAQ

### How does Manticore compare to angr?

Manticore is simpler. It has a smaller codebase, fewer dependencies and features, and an easier learning curve. If you
come from a reverse engineering or exploitation background, you may find Manticore intuitive due to its lack of intermediate representation and overall emphasis on staying close to machine abstractions.
