# manticore

[![Build Status](https://travis-ci.com/trailofbits/manticore.svg?token=m4YsYkGcyttTxRXGVHMr&branch=master)](https://travis-ci.com/trailofbits/manticore)

Manticore is a prototyping tool for dynamic binary analysis, with support for
symbolic execution, taint analysis, and binary instrumentation.

## features

- **Input Generation**: Manticore automatically generates inputs that trigger
  unique code paths.
- **Crash Discovery**: Manticore discovers inputs that crash programs via
memory safety violations.
- **Execution Tracing**: Manticore records an instruction-level trace of the
  program's execution for each generated input.
- **Programmatic Interface** (beta): Manticore exposes programmatic access
  to its analysis engine via a Python API.

## scope

Manticore supports binaries of the following formats, operating systems, and
architectures. It has been primarily used on binaries compiled from C and C++.

- OS/Formats: Linux ELF, Windows Minidump
- Architectures: x86, x86_64, ARMv7 (partial)

## requirements

Manticore is officially supported on Linux and uses Python 2.7.

## installation

From the root of the Manticore repository, run:

```
pip install .
````

or, if you would like to do a user install:

```
pip install --user .
```

This installs the Manticore CLI tool (`manticore`) and the Python API.

Then, install the Z3 Theorem Prover. Download the latest release for your
platform from https://github.com/Z3Prover/z3/releases/latest, and place the
enclosed `z3` binary in your `$PATH`.

> Note: Due to a known [issue](https://github.com/aquynh/capstone/issues/445),
  Capstone may not install correctly. If you get this error message,
  "ImportError: ERROR: fail to load the dynamic library.", or another related
  to Capstone, try reinstalling via `pip install -I --no-binary capstone capstone`

### for developers

For a dev install, run:

```
pip install -e .[dev]
```

This installs a few other dependencies used for tests, which you can run, for
example, with some of the commands below:

```
cd /path/to/manticore/
# all tests
nosetests
# just one file
nosetests test/test_armv7cpu.py
# just one test class
nosetests test/test_armv7cpu.py:Armv7CpuInstructions
# just one test
nosetests test/test_armv7cpu.py:Armv7CpuInstructions.test_mov_imm_min
```

## quick start

After installing Manticore, here is some basic usage you can try.

```
cd examples/linux
make
manticore basic  # a mcore_* directory is created
cat mcore_*/*1.stdin | ./basic
cat mcore_*/*2.stdin | ./basic

cd ../script
python count_instructions.py ../linux/helloworld
```

## usage

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
