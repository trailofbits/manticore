# Change Log

The format is based on [Keep a Changelog](http://keepachangelog.com/).

## [Unreleased](https://github.com/trailofbits/manticore/compare/0.1.10...HEAD)

## 0.1.10 - 2018-06-22

Thanks to our external contributors!

- [khorben](https://github.com/khorben)
- [catenacyber](https://github.com/catenacyber)
- [dwhjames](https://github.com/dwhjames)
- [matiasb](https://github.com/matiasb)
- [reaperhulk](https://github.com/reaperhulk)
- [lazzarello](https://github.com/lazzarello)

### Added

- ARM: New instructions to better support Raspberry Pi binaries (UTXH, UQSUB8)
- Linux: Can use `--env` and `LD_LIBRARY_PATH` to specify alternate ELF interpreter locations for dynamic binaries
- Linux: Partial chroot(2) and fork(2) models
- Initial support for NetBSD hosts
- Ethereum: `--avoid-constant` cli argument to enable heuristics to avoid unnecessary exploration of constant functions

### Changed

- Ethereum detectors are now opt-in, via cli flags: `--detect-overflow`, `--detect-invalid`, `--detect-uninitialized-memory`, `--detect-uninitialized-storage`, `--detect-all`
- Ethereum: Complete internal refactor.
    - Model memory using smtlib arrays to better support symbolic indexing
    - Numerous internal API improvements
    - Better symbolic gas support
    - More advanced overflow detection heuristics
    - Account names, scripts can assign names to accounts or contracts
    - Better ABI serializer/deserializer for canonical types, supports tuples/structs and recursive types
    - State list iterations improvements, modifications to state persist
    - Symbolic caller, address, value and data in transactions

### Fixed

- Linux: Generate concretized file content for symbolic files
- Linux: Fixes in various syscall models (brk, stat*), and miscellaneous fixes
- Ethereum: Inaccurate transaction history in some cases

## 0.1.9 - 2018-05-04

Thanks to our external contributors!

- [khorben](https://github.com/khorben)
- [arunjohnkuruvilla](https://github.com/arunjohnkuruvilla)
- [cclauss](https://github.com/cclauss)
- [dwhjames](https://github.com/dwhjames)
- [catenacyber](https://github.com/catenacyber)
- [disconnect3d](https://github.com/disconnect3d)

### Added

- Ethereum: `--txnocoverage` cli argument to suppress coverage based analysis halting criteria
- Ethereum: Support added for more Solidity features (imports, uint/int types, function types)

### Fixed

- Numerous Ethereum ABI fixes
- Linux and x86/64 emulation fixes
- Solver performance issue

## 0.1.8 - 2018-03-30

Thanks to our external contributors!

- [khorben](https://github.com/khorben)
- [disconnect3d](https://github.com/disconnect3d)
- [arunjohnkuruvilla](https://github.com/arunjohnkuruvilla)
- [mroll](https://github.com/mroll)

### Added

- Ethereum: `--txaccount` cli argument to control caller of transaction
- Ethereum: Per state execution trace files in workspace

### Fixed

- Linux: `--data` cli argument to specify concrete stdin
- Numerous Ethereum fixes and stability improvements
- Fixes for native cpu emulation

## 0.1.7 - 2018-02-23

This release brings EVM, performance, Linux emulation, and API improvements, along with numerous bug fixes. Thanks again to our external contributors!

- [jean](https://github.com/jean)
- [disconnect3d](https://github.com/disconnect3d)
- [arunjohnkuruvilla](https://github.com/arunjohnkuruvilla)
- [alexanderholman](https://github.com/alexanderholman)
- [Srinivas11789](https://github.com/Srinivas11789)

### Added

 - [Documentation](https://github.com/trailofbits/manticore/blob/master/docs/syminput.rst) on symbolic input
 - "[force](http://manticore.readthedocs.io/en/latest/api.html#manticore.core.cpu.abstractcpu.Cpu.write_bytes)" keyword argument in `cpu.write_bytes/read_bytes` etc.
 - Linux syscalls: getrandom(), openat()

### Fixed

- Improved ARMv7 Thumb support
- Numerous EVM bug fixes and improvements (transaction generation, SHA3 handling, instruction tracing, int overflow detection)
- Improved x86/64 emulation performance

## 0.1.6 - 2017-12-22

This release brings improved EVM support, performance improvements, and numerous bug fixes. Thanks to our external contributors!

- [cole-lightfighter](https://github.com/cole-lightfighter)
- [arunjohnkuruvilla](https://github.com/arunjohnkuruvilla)
- [Srinivas11789](https://github.com/Srinivas11789)
- [sidhant-gupta-004](https://github.com/sidhant-gupta-004)
- [roachspray](https://github.com/roachspray)
- [dbogs425](https://github.com/dbogs425)
- [HighW4y2H3ll](https://github.com/HighW4y2H3ll)
- [chowdaryd](https://github.com/chowdaryd)

### Added

- Ethereum support in the command line (Solidity files)
- --version, --txlimit flags to command line
- x86/64: Improved support for PCMPXSTRX instruction family
- Ethereum EVM assembly/disassembly APIs

### Changed

- Workspace .txt file extension changed to .input
- Ethereum EVM analysis APIs

### Fixed

- Deserializing Linux states with special files (/dev) opened
- Redundant forking performance issue fixed
- Various bugfixes in Decree, Linux, ARMv7 Thumb, Unicorn fallback emulation, Z3 Solver interface

## 0.1.5 - 2017-10-19

Thanks to our external contributors to this release!

- [johnfxgalea](https://github.com/johnfxgalea)

### Deprecated

- `Manticore('binary', ['arg1', 'arg2'])` style initialization. Use new class methods (see below).

### Added

- Platform-specific class methods for Manticore initialization
  - e.g. `Manticore.linux('binary', ['arg1', 'arg2'])`
- `Manticore.init` analysis initialization hook
- Linux: Various new syscall support, including basic TCP socket support
- Core: An updated plugin infrastructure
- [Experimental] Support for symbolic execution of Ethereum Virtual Machine bytecode

### Changed

- `Manticore.verbosity`: logging preset levels interface is now a static method, replacing `m.verbosity` property
- Logger output is slightly modified to be more Pythonic

### Fixed

- Numerous bugfixes and refactors
- Linux: stderr file is generated in workspace

### Removed

- Requirement of external z3 binary installation (z3 installation occurs automatically now via pip)

## 0.1.4 - 2017-08-18

### Added

- `Manticore.locked_context()` (safe parallel context access)
- `State.generate_testcase()` (arbitrary testcase generation from hooks)
- Documentation on [gotchas](http://manticore.readthedocs.io/en/latest/gotchas.html)
- Command line interface support for symbolic files (`--file`) (thanks [251](https://github.com/251)!)
- [Experimental] `State.context['branches']` (States track symbolic branches)
- [Experimental] Support for emulation of [Binary Ninja](https://binary.ninja) IL

### Changed

- Taint parameters added to `State.new_symbolic_buffer()` and `State.symbolicate_buffer()` (thanks [ehennenfent](https://github.com/ehennenfent)!)
- Improved support for ARM binaries
- `Manticore.verbosity` logging preset levels

### Fixed

- Numerous bugfixes
- Fixed workspace error message bug (thanks [chowdaryd](https://github.com/chowdaryd)!)
- Fixed double workspace bug

### Removed

- [Experimental] `State.generate_inputs()` (superseded by `State.generate_testcase()`)

## 0.1.3 - 2017-07-14

### Added

- Support for Redis as a storage backend, plus an API for user-defined serializers and storage backends
- "Events" which work as global signals for communication across manticore
- Support for using Binary Ninja for visualization
- Executor now provides a global shared context
- State now provides a local context

### Changed

- Refactored Executor and everything it talks to significantly
- Some older APIs may be broken or removed by the above refactor (`state.co` is no more, for instance)

### Fixed

- Numerous bugfixes and stability improvements in logging, Windows, x86, Linux

## 0.1.2 - 2017-06-14

### Added

- Function modeling API (`state.invoke_model()`, `manticore.variadic`)
- `strcmp` and `strlen` models
- `state.solve_buffer()`
- Additional `state` APIs
- Support for ARMv7 Thumb mode

### Changed

- Parallel processing API (`m.run(procs)`)
- `state.solve_n()`

### Fixed

- Numerous fixes in Linux, x86, ARM, SMT
- pip installation no longer requires `--no-binary capstone`

## 0.1.1 - 2017-05-05

### Added
- `State.constrain`

### Changed
- Command line verbosity: `--verbose` -> `-v` (up to `-vvvv`)

### Fixed
- Linux platform fixes: syscalls, ELF loading
- x86 and ARM fixes

## 0.1.0 - 2017-04-24

Initial public release.
