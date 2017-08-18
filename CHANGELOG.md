# Change Log

The format is based on [Keep a Changelog](http://keepachangelog.com/).

## [Unreleased](https://github.com/trailofbits/manticore/compare/0.1.4...HEAD)

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
