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
  to Capstone, try reinstalling via `pip install -I --no-binary capstone`

## quick start

After installing Manticore, here is some basic usage you can try.

```
cd examples/linux
make
manticore basic  # a pse_* directory is created
cat pse_*/*1.stdin | ./basic
cat pse_*/*2.stdin | ./basic

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

### How does Manticore compare to [angr](http://angr.io)?

In short, Manticore is simpler. Manticore is a smaller codebase, and has fewer
dependencies and features. Accordingly, Manticore may also be slower,
for example, due to having less symbolic execution optimizations and techniques
implemented.

Generally speaking, a subset of the analyses that can be implemented with angr,
can be implemented with Manticore, however if you’ve used neither, you may find
Manticore to have a slightly less steep learning curve. Additionally, if you
come from a reverse engineering or exploitation background, you may find
Manticore intuitive due to its lack of intermediate representation and overall
emphasis on staying close to machine abstractions.



