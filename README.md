# Manticore
<p align="center">
  <img src="docs/images/manticore.png?raw=true" width="256" title="Manticore">
</p>
<br />


[![Build Status](https://travis-ci.com/trailofbits/manticore.svg?branch=master)](https://travis-ci.com/trailofbits/manticore)
[![PyPI version](https://badge.fury.io/py/manticore.svg)](https://badge.fury.io/py/manticore)
[![Slack Status](https://empireslacking.herokuapp.com/badge.svg)](https://empireslacking.herokuapp.com)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)
[![Maintainability](https://api.codeclimate.com/v1/badges/9161568d8378cea903f4/maintainability)](https://codeclimate.com/github/trailofbits/manticore/maintainability)
[![Test Coverage](https://api.codeclimate.com/v1/badges/9161568d8378cea903f4/test_coverage)](https://codeclimate.com/github/trailofbits/manticore/test_coverage)

Manticore is a symbolic execution tool for analysis of smart contracts and binaries.

> Note: Beginning with version 0.2.0, Python 3.6+ is required.

## Features

- **Input Generation**: Manticore automatically generates inputs that trigger unique code paths
- **Error Discovery**: Manticore discovers bugs and produces inputs required to trigger them
- **Execution Tracing**: Manticore records an instruction-level trace of execution for each generated input
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore can analyze the following types of programs:

- Ethereum smart contracts (EVM bytecode)
- Linux ELF binaries (x86, x86_64 and ARMv7)

## Usage

### CLI

Manticore has a command line interface which can be used to easily symbolically execute a supported program or smart contract. Analysis results will be placed into a new directory beginning with `mcore_`.

Use the CLI to explore possible states in Ethereum smart contracts. Manticore includes _detectors_ that flag potentially vulnerable code in discovered states; output from them will be written to stdout and the results directory.
Solidity smart contracts must have a `.sol` extension for analysis by Manticore. See a [demo](https://asciinema.org/a/154012).

```bash
$ manticore ./path/to/contract.sol  # runs, and creates a mcore_* directory with analysis results
```

The command line can also be used to simply explore a Linux binary:

```bash
$ manticore ./path/to/binary        # runs, and creates a mcore_* directory with analysis results
$ manticore ./path/to/binary ab cd  # use concrete strings "ab", "cd" as program arguments
$ manticore ./path/to/binary ++ ++  # use two symbolic strings of length two as program arguments
```

### API

Manticore has a Python programming interface which can be used to implement custom analyses.

For Ethereum smart contracts, it can be used for detailed verification of arbitrary contract properties. Set starting conditions, execute symbolic transactions, then review discovered states to ensure invariants for your contract hold.

```python
from manticore.ethereum import ManticoreEVM
contract_src="""
contract Adder {
    function incremented(uint value) public returns (uint){
        if (value == 1)
            revert();
        return value + 1;
    }
}
"""
m = ManticoreEVM()

user_account = m.create_account(balance=1000)
contract_account = m.solidity_create_contract(contract_src,
                                              owner=user_account,
                                              balance=0)
value = m.make_symbolic_value()

contract_account.incremented(value)

for state in m.ready_states:
    print("can value be 1? {}".format(state.can_be_true(value == 1)))
    print("can value be 200? {}".format(state.can_be_true(value == 200)))
```

It is also possible to use the API to create custom analysis tools for Linux binaries.


```python
# example Manticore script
from manticore.native import Manticore

hook_pc = 0x400ca0

m = Manticore.linux('./path/to/binary')

@m.hook(hook_pc)
def hook(state):
  cpu = state.cpu
  print('eax', cpu.EAX)
  print(cpu.read_int(cpu.ESP))

  m.kill()  # tell Manticore to stop

m.run()
```

## Requirements

* Manticore is supported on Linux and requires **Python 3.6+**.
* Ubuntu 18.04 is strongly recommended.
* Ethereum smart contract analysis requires the [`solc`](https://github.com/ethereum/solidity) program in your `$PATH`.
* Increased stack size is recommended; this can be done by `ulimit -s 100000` or by passing `--ulimit stack=100000000:100000000` to `docker run` if docker is used.

## Quickstart

Install and try Manticore in a few shell commands:

```bash
# Install system dependencies
sudo apt-get update && sudo apt-get install python3 python3-pip -y

# Install Manticore and its dependencies
sudo pip3 install manticore[native]

# Download the examples
git clone https://github.com/trailofbits/manticore.git && cd manticore/examples/linux

# Build the examples
make

# Use the Manticore CLI
manticore basic
cat mcore_*/*0.stdin | ./basic
cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
cd ../script
python3 count_instructions.py ../linux/helloworld
```

You can also use Docker to quickly install and try Manticore:

```bash
# Run container with a shared examples/ directory
# Note that `--rm` will make the container be deleted if you exit it
# (if you want to persist data from the container, use docker volumes)
# (we need to increase maximum stack size, so we use ulimit for that)
$ docker run --rm -it --ulimit stack=100000000:100000000 trailofbits/manticore bash

# Change to examples directory
manticore@8d456f662d0f:~$ cd manticore/examples/linux/

# Build the examples
manticore@8d456f662d0f:~/manticore/examples/linux$ make

# Use the Manticore CLI
manticore@8d456f662d0f:~/manticore/examples/linux$ manticore basic


manticore@8d456f662d0f:~/manticore/examples/linux$ cat mcore_*/*0.stdin | ./basic
manticore@8d456f662d0f:~/manticore/examples/linux$ cat mcore_*/*1.stdin | ./basic

# Use the Manticore API
manticore@8d456f662d0f:~/manticore/examples/linux$ cd ../script
manticore@8d456f662d0f:~/manticore/examples/script$ python3 count_instructions.py ../linux/helloworld
```

## Installation


> NOTE: For native binary analysis, Manticore requires additional dependencies that are not installed by default. To
install these also, substitute `manticore[native]` for `manticore` in any `pip` command.


Option 1: Perform a user install (requires `~/.local/bin` in your `PATH`).

```bash
echo "PATH=\$PATH:~/.local/bin" >> ~/.profile
source ~/.profile
pip3 install --user manticore
```

Option 2: Use a virtual environment (requires [virtualenvwrapper](https://virtualenvwrapper.readthedocs.io/en/latest/) or [similar](https://virtualenv.pypa.io/en/stable/)).

```bash
sudo pip3 install virtualenvwrapper
echo "source /usr/local/bin/virtualenvwrapper.sh" >> ~/.profile
source ~/.profile
mkvirtualenv manticore
sudo ./manticore/bin/pip3 install manticore
```

Option 3: Perform a system install.

```bash
sudo pip3 install manticore
```

Option 4: Install via Docker.

```bash
docker pull trailofbits/manticore
```

Once installed, the `manticore` CLI tool and Python API will be available.

For installing a development version of Manticore, see our [wiki](https://github.com/trailofbits/manticore/wiki/Hacking-on-Manticore).

If you use Mac OS X you may need to install dependencies manually:

```bash
brew install capstone
export MACOS_UNIVERSAL=no && pip install capstone

brew install unicorn
UNICORN_QEMU_FLAGS="--python=`whereis python`" pip install unicorn
```

### Solidity Versions
Note that we're still in the process of implementing full support for the EVM Constantinople instruction semantics, so certain opcodes may not be supported.
You may want to consider using a version of `solc` that's less likely to generate these opcodes (eg pre-0.5.0).

## Getting Help

Feel free to stop by our #manticore slack channel in [Empire Hacking](https://empireslacking.herokuapp.com/) for help using or extending Manticore.


Documentation is available in several places:

  * The [wiki](https://github.com/trailofbits/manticore/wiki) contains some
    basic information about getting started with Manticore and contributing

  * The [examples](examples) directory has some very minimal examples that
    showcase API features

  * The [API reference](http://manticore.readthedocs.io/en/latest/) has more
    thorough and in-depth documentation on our API

  * The [manticore-examples](https://github.com/trailofbits/manticore-examples)
    repository has some more involved examples, for instance solving real CTF problems

## License

Manticore is licensed and distributed under the AGPLv3 license. [Contact us](mailto:opensource@trailofbits.com) if you're looking for an exception to the terms.
