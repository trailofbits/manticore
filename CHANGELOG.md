# Change Log

The format is based on [Keep a Changelog](http://keepachangelog.com/).

## [Unreleased](https://github.com/trailofbits/manticore/compare/0.1.2...HEAD)

## 0.1.2 - 2017-06-14

### Added

- Function modeling API (`state.invoke_model`, `manticore.variadic`)
- `strcmp` and `strlen` models
- `state.solve_buffer`
- Additional `state` APIs

### Changed

- Parallel processing API (`m.run(procs)`)
- `state.solve_n`

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