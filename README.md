# Manticore
<p align="center">
  <img src="docs/images/manticore.png?raw=true" width="256" title="Manticore">
</p>
<br />


[![Build Status](https://img.shields.io/github/workflow/status/trailofbits/manticore/CI/master)](https://github.com/trailofbits/manticore/actions?query=workflow%3ACI)
[![Codecov](https://img.shields.io/codecov/c/github/trailofbits/manticore)](https://codecov.io/github/trailofbits/manticore)
[![PyPI Version](https://badge.fury.io/py/manticore.svg)](https://badge.fury.io/py/manticore)
[![Slack Status](https://empireslacking.herokuapp.com/badge.svg)](https://empireslacking.herokuapp.com)
[![Documentation Status](https://readthedocs.org/projects/manticore/badge/?version=latest)](http://manticore.readthedocs.io/en/latest/?badge=latest)
[![Example Status](https://img.shields.io/github/workflow/status/trailofbits/manticore-examples/CI/master)](https://github.com/trailofbits/manticore-examples/actions?query=workflow%3ACI)
[![LGTM Total Alerts](https://img.shields.io/lgtm/alerts/g/trailofbits/manticore.svg?logo=lgtm&logoWidth=18)](https://lgtm.com/projects/g/trailofbits/manticore/alerts/)

Manticore is a symbolic execution tool for analysis of smart contracts and binaries.

## Features

- **Program Exploration**: Manticore can execute a program with symbolic inputs and explore all the possible states it can reach
- **Input Generation**: Manticore can automatically produce concrete inputs that result in a given program state
- **Error Discovery**: Manticore can detect crashes and other failure cases in binaries and smart contracts
- **Instrumentation**: Manticore provides fine-grained control of state exploration via event callbacks and instruction hooks
- **Programmatic Interface**: Manticore exposes programmatic access to its analysis engine via a Python API

Manticore can analyze the following types of programs:

- Ethereum smart contracts (EVM bytecode)
- Linux ELF binaries (x86, x86_64, aarch64, and ARMv7)
- WASM Modules

## Installation

> Note: We recommend installing Manticore in a [virtual environment](https://packaging.python.org/guides/installing-using-pip-and-virtual-environments/#installing-virtualenv)
 to prevent conflicts with other projects or packages

Option 1: Installing from PyPI:

```bash
pip install manticore
```

Option 2: Installing from PyPI, with extra dependencies needed to execute native binaries:

```bash
pip install "manticore[native]"
```

Option 3: Installing from the `master` branch:

```bash
git clone https://github.com/trailofbits/manticore.git
cd manticore
pip install -e ".[native]"
```

Option 4: Install via Docker:

```bash
docker pull trailofbits/manticore
```

Once installed, the `manticore` CLI tool and Python API will be available.

For a development installation, see our [wiki](https://github.com/trailofbits/manticore/wiki/Hacking-on-Manticore).

## Usage

### CLI

Manticore has a command line interface which can perform a basic symbolic analysis of a binary or smart contract. 
Analysis results will be placed into a workspace directory beginning with `mcore_`. For information about the workspace, see the [wiki](https://github.com/trailofbits/manticore/wiki/What's-in-the-workspace%3F).

#### EVM
Solidity smart contracts must have a `.sol` extension for analysis by Manticore. See a [demo](https://asciinema.org/a/154012).
<details>
  <summary>Click to expand:</summary>
  
```bash
$ manticore examples/evm/umd_example.sol 
 [9921] m.main:INFO: Registered plugins: DetectUninitializedMemory, DetectReentrancySimple, DetectExternalCallAndLeak, ...
 [9921] m.e.manticore:INFO: Starting symbolic create contract
 [9921] m.e.manticore:INFO: Starting symbolic transaction: 0
 [9921] m.e.manticore:INFO: 4 alive states, 6 terminated states
 [9921] m.e.manticore:INFO: Starting symbolic transaction: 1
 [9921] m.e.manticore:INFO: 16 alive states, 22 terminated states
[13761] m.c.manticore:INFO: Generated testcase No. 0 - STOP(3 txs)
[13754] m.c.manticore:INFO: Generated testcase No. 1 - STOP(3 txs)
...
[13743] m.c.manticore:INFO: Generated testcase No. 36 - THROW(3 txs)
[13740] m.c.manticore:INFO: Generated testcase No. 37 - THROW(3 txs)
[9921] m.c.manticore:INFO: Results in ~/manticore/mcore_gsncmlgx
```
</details>


#### Native
<details>
  <summary>Click to expand:</summary>
  
```bash
$ manticore examples/linux/basic
[9507] m.n.manticore:INFO: Loading program examples/linux/basic
[9507] m.c.manticore:INFO: Generated testcase No. 0 - Program finished with exit status: 0
[9507] m.c.manticore:INFO: Generated testcase No. 1 - Program finished with exit status: 0
[9507] m.c.manticore:INFO: Results in ~/manticore/mcore_7u7hgfay
[9507] m.n.manticore:INFO: Total time: 2.8029580116271973
```
</details>


### API

Manticore provides a Python programming interface which can be used to implement powerful custom analyses.

#### EVM
For Ethereum smart contracts, the API can be used for detailed verification of arbitrary contract properties. Users can set the starting conditions, 
execute symbolic transactions, then review discovered states to ensure invariants for a contract hold.
<details>
  <summary>Click to expand:</summary>
  
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
</details>

#### Native
It is also possible to use the API to create custom analysis tools for Linux binaries. Tailoring the initial state helps avoid state explosion
problems that commonly occur when using the CLI. 

<details>
  <summary>Click to expand:</summary>
  
```python
# example Manticore script
from manticore.native import Manticore

m = Manticore.linux('./example')

@m.hook(0x400ca0)
def hook(state):
  cpu = state.cpu
  print('eax', cpu.EAX)
  print(cpu.read_int(cpu.ESP))

  m.kill()  # tell Manticore to stop

m.run()
```
</details>


#### WASM
Manticore can also evaluate WebAssembly functions over symbolic inputs for property validation or general analysis. 

<details>
  <summary>Click to expand:</summary>
  
```python
from manticore.wasm import ManticoreWASM

m = ManticoreWASM("collatz.wasm")

def arg_gen(state):
    # Generate a symbolic argument to pass to the collatz function.
    # Possible values: 4, 6, 8
    arg = state.new_symbolic_value(32, "collatz_arg")
    state.constrain(arg > 3)
    state.constrain(arg < 9)
    state.constrain(arg % 2 == 0)
    return [arg]


# Run the collatz function with the given argument generator.
m.collatz(arg_gen)

# Manually collect return values
# Prints 2, 3, 8
for idx, val_list in enumerate(m.collect_returns()):
    print("State", idx, "::", val_list[0])
```
</details>

## Requirements
* Manticore requires Python 3.6 or greater 
* Manticore officially supports the latest LTS version of Ubuntu provided by Github Actions
  * Manticore has experimental support for EVM and WASM (but not native Linux binaries) on MacOS 
* We recommend running with increased stack size. This can be done by running `ulimit -s 100000` or by passing `--ulimit stack=100000000:100000000` to `docker run`

### Compiling Smart Contracts
* Ethereum smart contract analysis requires the [`solc`](https://github.com/ethereum/solidity) program in your `$PATH`.
* Manticore uses [crytic-compile](https://github.com/crytic/crytic-compile) to build smart contracts. If you're having compilation issues, consider running 
`crytic-compile` on your code directly to make it easier to identify any issues. 
* We're still in the process of implementing full support for the EVM Istanbul instruction semantics, so certain opcodes may not be supported.
In a pinch, you can try compiling with Solidity 0.4.x to avoid generating those instructions. 

## Getting Help

Feel free to stop by our #manticore slack channel in [Empire Hacking](https://empireslacking.herokuapp.com/) for help using or extending Manticore.

Documentation is available in several places:

  * The [wiki](https://github.com/trailofbits/manticore/wiki) contains information about getting started with Manticore and contributing

  * The [API reference](http://manticore.readthedocs.io/en/latest/) has more thorough and in-depth documentation on our API
    
  * The [examples](examples) directory has some small examples that showcase API features

  * The [manticore-examples](https://github.com/trailofbits/manticore-examples) repository has some more involved examples, including some real CTF problems

If you'd like to file a bug report or feature request, please use our [issues](https://github.com/trailofbits/manticore/issues/choose) page. 

For questions and clarifications, please visit the [discussion](https://github.com/trailofbits/manticore/discussions) page.

## License

Manticore is licensed and distributed under the AGPLv3 license. [Contact us](mailto:opensource@trailofbits.com) if you're looking for an exception to the terms.

## Publications
- [Manticore: A User-Friendly Symbolic Execution Framework for Binaries and Smart Contracts](https://arxiv.org/abs/1907.03890), Mark Mossberg, Felipe Manzano, Eric Hennenfent, Alex Groce, Gustavo Grieco, Josselin Feist, Trent Brunson, Artem Dinaburg - ASE 19

If you are using Manticore on an academic work, consider applying to the [Crytic $10k Research Prize](https://blog.trailofbits.com/2019/11/13/announcing-the-crytic-10k-research-prize/).

## Demo Video from ASE 2019
[![Brief Manticore demo video](https://img.youtube.com/vi/o6pmBJZpKAc/1.jpg)](https://youtu.be/o6pmBJZpKAc)

