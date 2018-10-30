# Change Log

The format is based on [Keep a Changelog](http://keepachangelog.com/).

## [Unreleased](https://github.com/trailofbits/manticore/compare/0.2.2...HEAD)

## 0.2.2 - 2018-10-30

### Added

- New API for generating a testcase only if a certain condition can be true in the state. Useful for conveniently
  checking an invariant in a state, and  (`ManticoreEVM.generate_testcase(..., only_if=)`) generating a testcase if it
  can be violated.
- New `constrain=` optional parameter for `State.solve_one` and `State.solve_buffer`. After solving for a symbolic variable,
  mutate the state by applying that solution as a constraint. Useful if concretizing a few symbolic variables, and later
  concretizations should take into account previously solved for values.
- `ManticoreEVM.human_transactions` top level API. Mirrors `ManticoreEVM.transactions`, but does not contain any internal
  transactions.
- Emit generated transaction data in human readable format (JSON)
- Warning messages if number of passed arguments to a Solidity function is inconsistent with the number declared
- CLI support for the ReentrancyAdvancedDetector
- Colored CLI output
- Configuration system. Allows configuration options to be specified in a config file. New configurations are available,
  notably including solver parameters such as solver timeout, and memory limits.
- Support for some unimplemented x86 XMM instructions
- Customizable symbolic stdin input buffer size

### Changed

- Improve the DetectExternalCallAndLeak detector and reduce false positives
- Numerous improvements and changes to the SolidityMetadata API

### Deprecated

- Several SolidityMetadata APIs: `.get_hash()`, `.functions`, `.hashes`

### Fixed

- Numerous fixes and enhancements to the Ethereum ABI implementation
- Better handling of overloaded functions in SolidityMetadata, and other bug fixes
- Fixes for the FilterFunctions plugin
- Fixes for symbolic SHA3 handling
- Many EVM correctness/consensus fixes
- Numerous spelling errors

## 0.2.1.1 - 2018-09-01

In this release, the codebase has been relicensed under the AGPLv3 license.
Please [contact us](opensource@trailofbits.com) if you're looking for an exception to these terms!

Thanks to our external contributors!

- [s0b0lev](https://github.com/s0b0lev)
- [redyoshi49q](https://github.com/redyoshi49q)

### Added
 
- Full suite of Ethereum detectors
    - Selfdestruct (`--detect-selfdestruct`): Warns if a selfdestruct instruction is reachable by the user
    - Ether Leak (`--detect-externalcall`): Warns if there is a call to the user, or a user controlled address, and ether can be sent.
    - External Call (`--detect-externalcall`): Warns if there is a call to the user, or a user controlled address.
    - Reentrancy (`--detect-reentrancy`): Warns if there is a change of storage state after a call to the user, or a user controlled address, with >2300 gas. This is an alternate implementation enabled in the CLI. The previous implementation is still available for API use (`DetectReentrancyAdvanced`).
    - Delegatecall (`--detect-delegatecall`): Warns if there is a delegatecall to a user controlled address, or to a user controlled function.
    - Environmental Instructions (`--detect-env`): Warns if certain instructions are used that can be potentially manipulated. Instructions: BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT, ORIGIN, GASPRICE.
- New Ethereum command line flags
    - `--no-testcases`: Do not generate testcases for discovered states
    - `--txnoether`: Do not make the transaction value symbolic in executed transactions
- SMTLIB: Advanced functionality for expression migration. Expressions from arbitrary constraint sets can be mixed to create arbitrary constraints, expressions are transparently migrated from constraint set to another, avoiding SMT naming collisions.
 
### Changed

- Command line interface uses new reentrancy detector based on detection of user controlled call addresses
 
### Fixed

- Ethereum: Support for overloaded solidity functions
- Ethereum: Significantly improved ability to create symbolic variables and constraints at the global level
- Ethereum: Improved gas support
- State serialization improvements and fixes

## 0.2.0 - 2018-08-10

In this release, the codebase has been ported to Python 3.6, which is a breaking change for API clients. Beginning with 0.2.0, client programs of Manticore must be compatible with Python 3.6.

Thanks to our external contributors!

- [ianklatzco](https://github.com/ianklatzco)
- [devtty1er](https://github.com/devtty1er)
- [catenacyber](https://github.com/catenacyber)

### Added

- Ethereum: More flexibility for Solidity compilation toolchains
- Ethereum: Detectors for unused return value, reentrancy
- Ethereum: Support for Solidity `bytesM` and `bytes` types
- Ethereum: Beta API for preconstraining inputs (`ManticoreEVM.constrain`)
- Improved performance for smtlib module
- Ability to transparently operate on bytearray and symbolic buffer (ArrayProxy) types (e.g: concatenate, slice)

### Changed

- **Codebase has been entirely ported to Python 3.6+**
- Ethereum: `ManticoreEVM.make_symbolic_value()` can be size adjustable
- Ethereum: Ethereum ABI (`manticore.ethereum.ABI`) API refactor, including real Solidity prototype parser
- Ethereum: Improved APIs for accessing transaction history
- Ethereum: Significant internal refactor

### Fixed

- Linux: Bugs related to handling of closed files
- Ethereum: Handling of symbolic callers/addresses
- Ethereum: Handling of gas handling on CALL instructions
- Various smtlib/expression fixes

### Removed

- Support for Python 2
- EVM disassembler/assembler module (EVMAsm) has been removed and separately released as [pyevmasm](https://github.com/trailofbits/pyevmasm)
- Experimental support for Binary Ninja IL emulation

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
- "Events" which work as global signals for communication across Manticore
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
