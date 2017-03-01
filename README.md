# manticore

[![Build Status](https://travis-ci.com/trailofbits/manticore.svg?token=m4YsYkGcyttTxRXGVHMr&branch=master)](https://travis-ci.com/trailofbits/manticore)

Manticore is a symbolic execution engine for binary analysis, usable as a
command line tool or Python Library (pre-alpha).

It executes multiple paths of a program simultaneously by replacing input data
with a set of constraints representing all possible values of that data,
allowing it to thoroughly discover numerous paths as the program executes
control flow. By solving the constraints with a theorem prover, Manticore
generates concrete inputs to trigger discovered paths.

## features

- **Input Generation**: Manticore automatically generates inputs that trigger
  unique code paths.
- **Defect Discovery**: Manticore discovers program defects enabling memory
  safety violations and generates inputs to trigger them.
- **Execution Tracing**: Manticore records an instruction-level trace of the
  program's execution for each generated input.
- **Concolic Execution**: Manticore loads memory dumps of running Windows
  programs to allow deep state space exploration.
- **Programmatic Interface** (pre-alpha): Manticore exposes programmatic access
  to its symbolic execution engine via a Python API.

## scope

Manticore supports binaries of the following formats, operating systems, and
architectures. It has been primarily used on binaries compiled from C and C++.

- OS/Formats: Linux ELF, Windows Minidump
- Architectures: x86, x86_64, ARMv7

## requirements

Manticore is officially supported on Linux and uses Python 2.7.

### required dependencies

- Python Dependencies: Run `pip install -r requirements.txt`
- Z3 Theorem Prover: Download the latest release for your platform from https://github.com/Z3Prover/z3/releases/latest, and place the enclosed `z3` binary in your `$PATH`.
  - Alternatively, CVC4 or Yices can be used.

### development dependencies

- keystone: Used in unit tests

## usage

```
python main.py ./path/to/binary  # runs, and creates a directory with analysis results
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
