import binascii
import json
import logging
import string
from multiprocessing import Queue, Process
from queue import Empty as EmptyQueue
from subprocess import check_output, Popen, PIPE
from typing import Dict, Optional, Union

import io
import os
import pyevmasm as EVMAsm
import random
import re
import sha3
import tempfile

from ..core.manticore import ManticoreBase
from ..core.smtlib import (
    ConstraintSet,
    Array,
    ArrayProxy,
    BitVec,
    Operators,
    BoolConstant,
    BoolOperation,
    Expression,
)
from ..core.state import TerminateState, AbandonState
from .account import EVMContract, EVMAccount, ABI
from .detectors import Detector
from .solidity import SolidityMetadata
from .state import State
from ..exceptions import EthereumError, DependencyError, NoAliveStates
from ..platforms import evm
from ..utils import config, log
from ..utils.helpers import PickleSerializer, issymbolic

logger = logging.getLogger(__name__)

cfg = config.get_group("evm")
cfg.add("defaultgas", 3000000, "Default gas value for ethereum transactions.")


def flagged(flag):
    """
    Return special character denoting concretization happened.
    """
    return "(*)" if flag else ""


def write_findings(method, lead_space, address, pc, at_init=""):
    """
    Writes contract address and EVM program counter indicating whether counter was read at constructor
    :param method: pointer to the object with the write method
    :param lead_space: leading white space
    :param address: contract address
    :param pc: program counter
    :param at_init: Boolean
    :return: pass
    """
    method.write(f"{lead_space}Contract: {address:#x}")
    method.write(
        f'{lead_space}EVM Program counter: {pc:#x}{" (at constructor)" if at_init else ""}\n'
    )


def calculate_coverage(runtime_bytecode, seen):
    """ Calculates what percentage of runtime_bytecode has been seen """
    count, total = 0, 0
    bytecode = SolidityMetadata._without_metadata(runtime_bytecode)
    for i in EVMAsm.disassemble_all(bytecode):
        if i.pc in seen:
            count += 1
        total += 1

    if total == 0:
        # No runtime_bytecode
        return 0
    return count * 100.0 / total


class ManticoreEVM(ManticoreBase):
    """ Manticore EVM manager

        Usage Ex::

            from manticore.ethereum import ManticoreEVM, ABI
            m = ManticoreEVM()
            #And now make the contract account to analyze
            source_code = '''
                pragma solidity ^0.4.15;
                contract AnInt {
                    uint private i=0;
                    function set(uint value){
                        i=value
                    }
                }
            '''
            #Initialize user and contracts
            user_account = m.create_account(balance=1000)
            contract_account = m.solidity_create_contract(source_code, owner=user_account, balance=0)
            contract_account.set(12345, value=100)

            m.finalize()
    """

    def make_symbolic_buffer(self, size, name=None, avoid_collisions=False):
        """ Creates a symbolic buffer of size bytes to be used in transactions.
            You can operate on it normally and add constraints to manticore.constraints
            via manticore.constrain(constraint_expression)

            Example use::

                symbolic_data = m.make_symbolic_buffer(320)
                m.constrain(symbolic_data[0] == 0x65)
                m.transaction(caller=attacker_account,
                                address=contract_account,
                                data=symbolic_data,
                                value=100000 )
        """
        if name is None:
            name = "TXBUFFER"
            avoid_collisions = True

        return self.constraints.new_array(
            index_bits=256,
            name=name,
            index_max=size,
            value_bits=8,
            taint=frozenset(),
            avoid_collisions=avoid_collisions,
        )

    def make_symbolic_value(self, nbits=256, name=None):
        """ Creates a symbolic value, normally a uint256, to be used in transactions.
            You can operate on it normally and add constraints to manticore.constraints
            via manticore.constrain(constraint_expression)

            Example use::

                symbolic_value = m.make_symbolic_value()
                m.constrain(symbolic_value > 100)
                m.constrain(symbolic_value < 1000)
                m.transaction(caller=attacker_account,
                                address=contract_account,
                                data=data,
                                value=symbolic_value )

        """
        avoid_collisions = False
        if name is None:
            name = "TXVALUE"
            avoid_collisions = True
        return self.constraints.new_bitvec(nbits, name=name, avoid_collisions=avoid_collisions)

    def make_symbolic_address(self, name=None, select="both"):
        """
        Creates a symbolic address and constrains it to pre-existing addresses or the 0 address.

        :param name: Name of the symbolic variable. Defaults to 'TXADDR' and later to 'TXADDR_<number>'
        :param select: Whether to select contracts or normal accounts. Not implemented for now.
        :return: Symbolic address in form of a BitVecVariable.
        """
        if select not in ("both", "normal", "contract"):
            raise EthereumError("Wrong selection type")
        if select in ("normal", "contract"):
            # FIXME need to select contracts or normal accounts
            raise NotImplemented

        avoid_collisions = False
        if name is None:
            name = "TXADDR"
            avoid_collisions = True

        symbolic_address = self.constraints.new_bitvec(
            160, name=name, avoid_collisions=avoid_collisions
        )

        constraint = symbolic_address == 0
        for account in self._accounts.values():
            constraint = Operators.OR(symbolic_address == int(account), constraint)
        self.constrain(constraint)

        return symbolic_address

    def constrain(self, constraint):
        if self.count_states() == 0:
            self.constraints.add(constraint)
        else:
            for state in self.all_states:
                state.constrain(constraint)

    @staticmethod
    def compile(
        source_code,
        contract_name=None,
        libraries=None,
        runtime=False,
        solc_bin=None,
        solc_remaps=[],
    ):
        """ Get initialization bytecode from a Solidity source code """
        name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings = ManticoreEVM._compile(
            source_code, contract_name, libraries, solc_bin, solc_remaps
        )
        if runtime:
            return runtime_bytecode
        return init_bytecode

    @staticmethod
    def _link(bytecode, libraries=None):
        has_dependencies = "_" in bytecode
        hex_contract = bytecode
        if has_dependencies:
            deps = {}
            pos = 0
            while pos < len(hex_contract):
                if hex_contract[pos] == "_":
                    lib_placeholder = hex_contract[pos : pos + 40]
                    # This is all very weak...
                    # Contract names starting/ending with _ ?
                    # Contract names longer than 40 bytes ?
                    if ":" in lib_placeholder:
                        # __/tmp/tmp_9k7_l:Manticore______________
                        lib_name = lib_placeholder.split(":")[1].strip("_")
                        deps.setdefault(lib_name, []).append(pos)
                    else:
                        lib_name = lib_placeholder.strip("_")
                        deps.setdefault(lib_name, []).append(pos)
                    pos += 40
                else:
                    pos += 2

            if libraries is None:
                raise DependencyError(deps.keys())
            libraries = dict(libraries)
            hex_contract_lst = list(hex_contract)
            for lib_name, pos_lst in deps.items():
                try:
                    lib_address = libraries[lib_name]
                except KeyError:
                    raise DependencyError([lib_name])
                for pos in pos_lst:
                    hex_contract_lst[pos : pos + 40] = "%040x" % int(lib_address)
            hex_contract = "".join(hex_contract_lst)
        return bytearray(binascii.unhexlify(hex_contract))

    @staticmethod
    def _run_solc(source_file, solc_bin=None, solc_remaps=[], working_dir=None):
        """ Compile a source file with the Solidity compiler

            :param source_file: a file object for the source file
            :param solc_bin: path to solc binary
            :param solc_remaps: solc import remaps
            :return: output, warnings
        """
        if solc_bin is not None:
            solc = solc_bin
        else:
            solc = "solc"

        # check solc version
        supported_versions = ("0.4.18", "0.4.21")

        try:
            installed_version_output = check_output([solc, "--version"])
        except OSError:
            raise EthereumError("Solidity compiler not installed.")

        m = re.match(
            r".*Version: (?P<version>(?P<major>\d+)\.(?P<minor>\d+)\.(?P<build>\d+)).*\+(?P<commit>[^\s]+).*",
            installed_version_output.decode(),
            re.DOTALL | re.IGNORECASE,
        )

        if not m or m.groupdict()["version"] not in supported_versions:
            # Fixme https://github.com/trailofbits/manticore/issues/847
            # logger.warning("Unsupported solc version %s", installed_version)
            pass

        # solc path search is a mess
        # https://solidity.readthedocs.io/en/latest/layout-of-source-files.html

        relative_filepath = source_file.name

        if not working_dir:
            working_dir = os.getcwd()

        if relative_filepath.startswith(working_dir):
            relative_filepath = relative_filepath[len(working_dir) + 1 :]

        # If someone pass an absolute path to the file, we don't have to put cwd
        additional_kwargs = {"cwd": working_dir} if working_dir else {}

        solc_invocation = (
            [solc]
            + list(solc_remaps)
            + [
                "--combined-json",
                "abi,srcmap,srcmap-runtime,bin,hashes,bin-runtime",
                "--allow-paths",
                ".",
                relative_filepath,
            ]
        )
        logger.debug(f"Running: {' '.join(solc_invocation)}")
        p = Popen(solc_invocation, stdout=PIPE, stderr=PIPE, **additional_kwargs)
        stdout, stderr = p.communicate()

        stdout, stderr = stdout.decode(), stderr.decode()

        # See #1123 - solc fails when run within snap
        # and https://forum.snapcraft.io/t/interfaces-allow-access-tmp-directory/5129
        if stdout == "" and f'""{relative_filepath}"" is not found' in stderr:
            raise EthereumError(
                "Solidity compilation failed with error: {}\n"
                "Did you install solc from snap Linux universal packages?\n"
                "If so, the problem is likely due to snap's sandbox restricting access to /tmp\n"
                "\n"
                "Here are some potential solutions:\n"
                " 1) Remove solc from snap and install it different way\n"
                " 2) Reinstall solc from snap in developer mode, so there is no sandbox\n"
                " 3) Find a way to add /tmp to the solc's sandbox. If you do, "
                "send us a PR so we could add it here!".format(stderr)
            )

        try:
            return json.loads(stdout), stderr
        except ValueError:
            raise EthereumError("Solidity compilation error:\n\n{}".format(stderr))

    @staticmethod
    def _compile(
        source_code, contract_name, libraries=None, solc_bin=None, solc_remaps=[], working_dir=None
    ):
        """ Compile a Solidity contract, used internally

            :param source_code: solidity source as either a string or a file handle
            :param contract_name: a string with the name of the contract to analyze
            :param libraries: an itemizable of pairs (library_name, address)
            :param solc_bin: path to solc binary
            :param solc_remaps: solc import remaps
            :param working_dir: working directory for solc compilation (defaults to current)
            :return: name, source_code, bytecode, srcmap, srcmap_runtime, hashes
            :return: name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings
        """

        if isinstance(source_code, str):
            with tempfile.NamedTemporaryFile("w+") as temp:
                temp.write(source_code)
                temp.flush()
                output, warnings = ManticoreEVM._run_solc(
                    temp, solc_bin, solc_remaps, working_dir=working_dir
                )
        elif isinstance(source_code, io.IOBase):
            output, warnings = ManticoreEVM._run_solc(
                source_code, solc_bin, solc_remaps, working_dir=working_dir
            )
            source_code.seek(0)
            source_code = source_code.read()
        else:
            raise TypeError(f"source code bad type: {type(source_code).__name__}")

        contracts = output.get("contracts", [])
        if len(contracts) != 1 and contract_name is None:
            raise EthereumError(
                f'Solidity file must contain exactly one contract or you must use a `--contract` parameter to specify one. Contracts found: {", ".join(contracts)}'
            )

        name, contract = None, None
        if contract_name is None:
            name, contract = list(contracts.items())[0]
        else:
            for n, c in contracts.items():
                if n == contract_name or n.split(":")[1] == contract_name:
                    name, contract = n, c
                    break

        if name is None:
            raise ValueError(f"Specified contract not found: {contract_name}")

        name = name.split(":")[1]

        if contract["bin"] == "":
            raise EthereumError(
                "Solidity failed to generate bytecode for your contract. Check if all the abstract functions are implemented"
            )

        bytecode = ManticoreEVM._link(contract["bin"], libraries)
        srcmap = contract["srcmap"].split(";")
        srcmap_runtime = contract["srcmap-runtime"].split(";")
        hashes = {str(x): str(y) for x, y in contract["hashes"].items()}
        abi = json.loads(contract["abi"])
        runtime = ManticoreEVM._link(contract["bin-runtime"], libraries)
        return name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings

    @property
    def accounts(self):
        return dict(self._accounts)

    def account_name(self, address):
        for name, account in self._accounts.items():
            if account.address == address:
                return name
        return "0x{:x}".format(address)

    @property
    def normal_accounts(self):
        return {
            name: account
            for name, account in self._accounts.items()
            if not isinstance(account, EVMContract)
        }

    @property
    def contract_accounts(self):
        return {
            name: account
            for name, account in self._accounts.items()
            if isinstance(account, EVMContract)
        }

    def get_account(self, name):
        return self._accounts[name]

    def __init__(self, workspace_url: str = None, policy: str = "random"):
        """
        A Manticore EVM manager
        :param workspace_url: workspace folder name
        :param policy: scheduling priority
        """
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        super().__init__(initial_state, workspace_url=workspace_url, policy=policy)
        self.subscribe("will_terminate_state", self._terminate_state_callback)
        self.subscribe("did_evm_execute_instruction", self._did_evm_execute_instruction_callback)
        self.subscribe("did_read_code", self._did_evm_read_code)
        self.subscribe("on_symbolic_sha3", self._on_symbolic_sha3_callback)
        self.subscribe("on_concrete_sha3", self._on_concrete_sha3_callback)

        self._accounts = dict()
        self._serializer = PickleSerializer()

        self.constraints = constraints
        self.detectors = {}
        self.metadata: Dict[int, SolidityMetadata] = {}

        # The following should go to manticore.context so we can use multiprocessing
        with self.locked_context("ethereum", dict) as context:
            context["_sha3_states"] = dict()
            context["_known_sha3"] = set()

    @property
    def world(self):
        """ The world instance or None if there is more than one state """
        return self.get_world()

    # deprecate this 5 in favor of for state in m.all_states: do stuff?
    @property
    def completed_transactions(self):
        logger.info("Deprecated!")
        with self.locked_context("ethereum") as context:
            return context["_completed_transactions"]

    def get_world(self, state_id=None):
        """ Returns the evm world of `state_id` state. """
        logger.info("Deprecated!")
        if state_id is None:
            state_id = self._ready_states[0]

        state = self._load(state_id)
        if state is None:
            return None
        else:
            return state.platform

    def get_balance(self, address, state_id=None):
        """ Balance for account `address` on state `state_id` """
        logger.info("Deprecated!")
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_balance(address)

    def get_storage_data(self, address, offset, state_id=None):
        """ Storage data for `offset` on account `address` on state `state_id` """
        logger.info("Deprecated!")
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_storage_data(address, offset)

    def get_code(self, address, state_id=None):
        """ Storage data for `offset` on account `address` on state `state_id` """
        logger.info("Deprecated!")
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_code(address)

    def last_return(self, state_id=None):
        """ Last returned buffer for state `state_id` """
        logger.info("Deprecated!")
        state = self.load(state_id)
        return state.platform.last_transaction.return_data

    def transactions(self, state_id=None):
        """ Transactions list for state `state_id` """
        logger.info("Deprecated!")
        state = self._load(state_id)
        return state.platform.transactions

    def human_transactions(self, state_id=None):
        """ Transactions list for state `state_id` """
        logger.info("Deprecated!")
        state = self.load(state_id)
        return state.platform.human_transactions

    def make_symbolic_arguments(self, types):
        """
            Build a reasonable set of symbolic arguments matching the types list
        """
        from . import abitypes

        return self._make_symbolic_arguments(abitypes.parse(types))

    def _make_symbolic_arguments(self, ty):
        """ This makes a tuple of symbols to be used as arguments of type ty"""

        # If the types describe an string or an array this will produce strings
        # or arrays of a default size.
        # TODO: add a configuration constant for these two
        default_string_size = 32
        default_array_size = 32
        if ty[0] in ("int", "uint"):
            result = self.make_symbolic_value()
        elif ty[0] == "bytesM":
            result = self.make_symbolic_buffer(size=ty[1])
        elif ty[0] == "function":
            address = self.make_symbolic_value()
            func_id = self.make_symbolic_buffer(size=4)
            result = (address, func_id)
        elif ty[0] in ("bytes", "string"):
            result = self.make_symbolic_buffer(size=default_string_size)
        elif ty[0] == "tuple":
            result = ()
            for ty_i in ty[1]:
                result += (self._make_symbolic_arguments(ty_i),)
        elif ty[0] == "array":
            result = []
            rep = ty[1]
            if rep is None:
                rep = default_array_size
            for _ in range(rep):
                result.append(self._make_symbolic_arguments(ty[2]))
        else:
            raise NotImplemented

        return result

    def json_create_contract(
        self,
        jfile,
        owner=None,
        name=None,
        contract_name=None,
        balance=0,
        gas=None,
        network_id=None,
        args=(),
    ):
        """ Creates a solidity contract based on a truffle json artifact.
            https://github.com/trufflesuite/truffle/tree/develop/packages/truffle-contract-schema
            :param jfile: truffle json artifact
            :type jfile: str or IOBase
            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param contract_name: Name of the contract to analyze (optional if there is a single one in the source code)
            :type contract_name: str
            :param balance: balance to be transferred on creation
            :type balance: int or BitVecVariable
            :param gas: gas budget for each contract creation needed (may be more than one if several related contracts defined in the solidity source)
            :type gas: int
            :param network_id: Truffle network id to instantiate
            :param tuple args: constructor arguments
            :rtype: EVMAccount
        """

        if isinstance(jfile, io.IOBase):
            jfile = jfile.read()
        elif isinstance(jfile, bytes):
            jfile = str(jfile, "utf-8")
        elif not isinstance(jfile, str):
            raise TypeError(f"source code bad type: {type(jfile).__name__}")

        truffle = json.loads(jfile)
        hashes = {}
        for item in truffle["abi"]:
            item_type = item["type"]
            if item_type in ("function"):
                signature = SolidityMetadata.function_signature_for_name_and_inputs(
                    item["name"], item["inputs"]
                )
                hashes[signature] = sha3.keccak_256(signature.encode()).hexdigest()[:8]
                if "signature" in item:
                    if item["signature"] != f"0x{hashes[signature]}":
                        raise Exception(
                            f"Something wrong with the sha3 of the method {signature} signature (a.k.a. the hash)"
                        )

        if contract_name is None:
            contract_name = truffle["contractName"]

        if network_id is None:
            if len(truffle["networks"]) > 1:
                raise Exception("Network id not specified")
            if len(truffle["networks"]) == 1:
                network_id = list(truffle["networks"].keys())[0]
        if network_id in truffle["networks"]:
            temp_dict = truffle["networks"][network_id]["links"]
            links = dict((k, int(v["address"], 0)) for k, v in temp_dict.items())
        else:
            links = ()

        source_code = truffle["source"]
        bytecode = self._link(truffle["bytecode"][2:], links)
        runtime = self._link(truffle["deployedBytecode"][2:], links)
        if "sourceMap" in truffle:
            srcmap = truffle["sourceMap"].split(";")
        else:
            srcmap_runtime = []
        if "deployedSourceMap" in truffle:
            srcmap_runtime = truffle["deployedSourceMap"].split(";")
        else:
            srcmap_runtime = []
        abi = truffle["abi"]
        md = SolidityMetadata(
            contract_name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, b""
        )
        constructor_types = md.get_constructor_arguments()
        if constructor_types != "()":
            if args is None:
                args = self.make_symbolic_arguments(constructor_types)

            constructor_data = ABI.serialize(constructor_types, *args)
        else:
            constructor_data = b""

        contract_account = self.create_contract(
            owner=owner, balance=balance, init=md._init_bytecode + constructor_data, gas=gas
        )

        if contract_account is None:
            raise EthereumError(f"Failed to build contract {contract_name}")
        self.metadata[int(contract_account)] = md

        if not self.count_ready_states() or len(self.get_code(contract_account)) == 0:
            return None
        return contract_account

    def solidity_create_contract(
        self,
        source_code,
        owner,
        name=None,
        contract_name=None,
        libraries=None,
        balance=0,
        address=None,
        args=(),
        solc_bin=None,
        solc_remaps=[],
        working_dir=None,
        gas=None,
    ):
        """ Creates a solidity contract and library dependencies

            :param str source_code: solidity source code
            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param contract_name: Name of the contract to analyze (optional if there is a single one in the source code)
            :type contract_name: str
            :param balance: balance to be transferred on creation
            :type balance: int or BitVecVariable
            :param address: the address for the new contract (optional)
            :type address: int or EVMAccount
            :param tuple args: constructor arguments
            :param solc_bin: path to solc binary
            :type solc_bin: str
            :param solc_remaps: solc import remaps
            :type solc_remaps: list of str
            :param working_dir: working directory for solc compilation (defaults to current)
            :type working_dir: str
            :param gas: gas budget for each contract creation needed (may be more than one if several related contracts defined in the solidity source)
            :type gas: int
            :rtype: EVMAccount
        """
        if libraries is None:
            deps = {}
        else:
            deps = dict(libraries)

        contract_names = [contract_name]
        while contract_names:
            contract_name_i = contract_names.pop()
            try:
                compile_results = self._compile(
                    source_code,
                    contract_name_i,
                    libraries=deps,
                    solc_bin=solc_bin,
                    solc_remaps=solc_remaps,
                    working_dir=working_dir,
                )
                md = SolidityMetadata(*compile_results)
                if contract_name_i == contract_name:
                    constructor_types = md.get_constructor_arguments()

                    if constructor_types != "()":
                        if args is None:
                            args = self.make_symbolic_arguments(constructor_types)

                        constructor_data = ABI.serialize(constructor_types, *args)
                    else:
                        constructor_data = b""

                    if balance != 0:
                        if not md.constructor_abi["payable"]:
                            raise EthereumError(
                                f"Can't create solidity contract with balance ({balance}) "
                                f"different than 0 because the contract's constructor is not payable."
                            )
                        elif self.world.get_balance(owner.address) < balance:
                            raise EthereumError(
                                f"Can't create solidity contract with balance ({balance}) "
                                f"because the owner account ({owner}) has insufficient balance "
                                f"({self.world.get_balance(owner.address)})."
                            )

                    contract_account = self.create_contract(
                        owner=owner,
                        balance=balance,
                        address=address,
                        init=md._init_bytecode + constructor_data,
                        name=name,
                        gas=gas,
                    )
                else:
                    contract_account = self.create_contract(owner=owner, init=md._init_bytecode)

                if contract_account is None:
                    raise EthereumError("Failed to build contract %s" % contract_name_i)
                self.metadata[int(contract_account)] = md

                deps[contract_name_i] = contract_account
            except DependencyError as e:
                contract_names.append(contract_name_i)
                for lib_name in e.lib_names:
                    if lib_name not in deps:
                        contract_names.append(lib_name)
            except Exception as e:
                self.kill()
                raise

        # If the contract was created successfully in at least 1 state return account
        for state in self.ready_states:
            if state.platform.get_code(int(contract_account)):
                return contract_account
        return None

    def get_nonce(self, address):
        # type forgiveness:
        address = int(address)
        # get all nonces for states containing this address:
        nonces = set(
            state.platform.get_nonce(address)
            for state in self.ready_states
            if address in state.platform
        )
        if not nonces:
            raise NoAliveStates("There are no alive states containing address %x" % address)
        elif len(nonces) != 1:
            # if there are multiple states with this address, they all have to have the same nonce:
            raise EthereumError(
                "Cannot increase the nonce of address %x because it exists in multiple states with different nonces"
                % address
            )
        else:
            return next(iter(nonces))

    def create_contract(self, owner, balance=0, address=None, init=None, name=None, gas=None):
        """ Creates a contract

            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transferred on creation
            :type balance: int or BitVecVariable
            :param int address: the address for the new contract (optional)
            :param str init: initializing evm bytecode and arguments
            :param str name: a unique name for reference
            :param gas: gas budget for the creation/initialization of the contract
            :rtype: EVMAccount
        """
        if not self.count_ready_states():
            raise NoAliveStates

        nonce = self.get_nonce(owner)
        expected_address = evm.EVMWorld.calculate_new_address(int(owner), nonce=nonce)

        if address is None:
            address = expected_address
        elif address != expected_address:
            raise EthereumError(
                "Address was expected to be %x but was given %x" % (expected_address, address)
            )

        # Name check
        if name is None:
            name = self._get_uniq_name("contract")
        if name in self._accounts:
            # Account name already used
            raise EthereumError("Name already used")

        self._transaction("CREATE", owner, balance, address, data=init, gaslimit=gas)
        # TODO detect failure in the constructor

        self._accounts[name] = EVMContract(
            address=address, manticore=self, default_caller=owner, name=name
        )
        return self.accounts[name]

    def _get_uniq_name(self, stem):
        count = 0
        for name_i in self.accounts.keys():
            if name_i.startswith(stem):
                try:
                    count = max(count, int(name_i[len(stem) :]) + 1)
                except Exception:
                    pass
        name = "{:s}{:d}".format(stem, count)
        assert name not in self.accounts
        return name

    def _all_addresses(self):
        """ Returns all addresses in all running states """
        ret = set()
        for state in self.ready_states:
            ret |= set(state.platform.accounts)
        return ret

    def new_address(self):
        """ Create a fresh 160bit address """
        all_addresses = self._all_addresses()
        while True:
            new_address = random.randint(100, pow(2, 160))
            if new_address not in all_addresses:
                return new_address

    def transaction(self, caller, address, value, data, gas=None):
        """ Issue a symbolic transaction in all running states

            :param caller: the address of the account sending the transaction
            :type caller: int or EVMAccount
            :param address: the address of the contract to call
            :type address: int or EVMAccount
            :param value: balance to be transfered on creation
            :type value: int or BitVecVariable
            :param data: initial data
            :param gas: gas budget
            :raises NoAliveStates: if there are no alive states to execute
        """
        self._transaction("CALL", caller, value=value, address=address, data=data, gaslimit=gas)

    def create_account(self, balance=0, address=None, code=None, name=None):
        """ Low level creates an account. This won't generate a transaction.

            :param balance: balance to be set on creation (optional)
            :type balance: int or BitVecVariable
            :param address: the address for the new account (optional)
            :type address: int
            :param code: the runtime code for the new account (None means normal account), str or bytes (optional)
            :param name: a global account name eg. for use as reference in the reports (optional)
            :return: an EVMAccount
        """
        # Need at least one state where to apply this
        if not self.count_ready_states():
            raise NoAliveStates

        # Name check
        if name is None:
            if code is None:
                name = self._get_uniq_name("normal")
            else:
                name = self._get_uniq_name("contract")
        if name in self._accounts:
            # Account name already used
            raise EthereumError("Name already used")

        # Balance check
        if not isinstance(balance, int):
            raise EthereumError("Balance invalid type")

        if isinstance(code, str):
            code = bytes(code, "utf-8")
        if code is not None and not isinstance(code, (bytes, Array)):
            raise EthereumError("code bad type")

        # Address check
        # Let's just choose the address ourself. This is not yellow paper material
        if address is None:
            address = self.new_address()
        if not isinstance(address, int):
            raise EthereumError("A concrete address is needed")
        assert address is not None
        if address in map(int, self.accounts.values()):
            # Address already used
            raise EthereumError("Address already used")

        # To avoid going full crazy we maintain a global list of addresses
        # Different states may CREATE a different set of accounts.
        # Accounts created by a human have the same address in all states.
        for state in self.ready_states:
            world = state.platform

            if "_pending_transaction" in state.context:
                raise EthereumError("This is bad. There should not be a pending transaction")

            if address in world.accounts:
                # Address already used
                raise EthereumError(
                    "This is bad. Same address is used for different contracts in different states"
                )
            world.create_account(address, balance, code=code, storage=None)

        self._accounts[name] = EVMAccount(address, manticore=self, name=name)
        return self.accounts[name]

    def _migrate_tx_expressions(self, state, caller, address, value, data):
        # Copy global constraints into each state.
        # We should somehow remember what has been copied to each state
        # In a second transaction we should only add new constraints.
        # And actually only constraints related to whatever we are using in
        # the tx. This is a FIXME
        global_constraints = self.constraints

        # Normally users will be making these symbolic expressions by creating
        # global symbolic variables via ManticoreEVM.make_.... and those
        # global expressions need to be imported into each state when a tx
        # actually happens

        if issymbolic(caller):
            caller = state.migrate_expression(caller)

        if issymbolic(address):
            address = state.migrate_expression(address)

        if issymbolic(value):
            value = state.migrate_expression(value)

        if issymbolic(data):
            if isinstance(data, ArrayProxy):  # FIXME is this necessary here?
                data = data.array
            data = state.migrate_expression(data)
            if isinstance(data, Array):
                data = ArrayProxy(data)

        for c in global_constraints:
            state.constrain(c)

        return caller, address, value, data

    def _transaction(self, sort, caller, value=0, address=None, data=None, gaslimit=None, price=1):
        """ Initiates a transaction

            :param caller: caller account
            :type caller: int or EVMAccount
            :param int address: the address for the transaction (optional)
            :param value: value to be transferred
            :param price: the price of gas for this transaction. Mostly unused.
            :type value: int or BitVecVariable
            :param str data: initializing evm bytecode and arguments or transaction call data
            :param gaslimit: gas budget
            :rtype: EVMAccount
        """
        if gaslimit is None:
            gaslimit = cfg.defaultgas
        # Type Forgiveness
        if isinstance(address, EVMAccount):
            address = int(address)
        if isinstance(caller, EVMAccount):
            caller = int(caller)
        # Defaults, call data is empty
        if data is None:
            data = bytearray(b"")
        if isinstance(data, (str, bytes)):
            data = bytearray(data)
        if not isinstance(data, (bytearray, Array)):
            raise TypeError("code bad type")

        # Check types
        if not isinstance(caller, (int, BitVec)):
            raise TypeError("Caller invalid type")

        if not isinstance(value, (int, BitVec)):
            raise TypeError("Value invalid type")

        if not isinstance(address, (int, BitVec)):
            raise TypeError("address invalid type")

        if not isinstance(price, int):
            raise TypeError("Price invalid type")

        # Check argument consistency and set defaults ...
        if sort not in ("CREATE", "CALL"):
            raise ValueError("unsupported transaction type")

        if sort == "CREATE":
            # When creating data is the init_bytecode + arguments
            if len(data) == 0:
                raise EthereumError("An initialization bytecode is needed for a CREATE")

        assert address is not None
        assert caller is not None

        # Transactions (like everything else) need at least one running state
        if not self.count_ready_states():
            raise NoAliveStates

        # To avoid going full crazy, we maintain a global list of addresses
        for state in self.ready_states:
            world = state.platform

            # if '_pending_transaction' in state.context:
            #    raise EthereumError("This is bad. It should not be a pending transaction")

            # Choose an address here, because it will be dependent on the caller's nonce in this state
            if address is None:
                if issymbolic(caller):
                    # TODO (ESultanik): In order to handle this case, we are going to have to do something like fork
                    # over all possible caller addresses.
                    # But this edge case will likely be extremely rare, if ever ecountered.
                    raise EthereumError(
                        "Manticore does not currently support contracts with symbolic addresses creating new contracts"
                    )
                address = world.new_address(caller)

            # Migrate any expression to state specific constraint set
            caller_migrated, address_migrated, value_migrated, data_migrated = self._migrate_tx_expressions(
                state, caller, address, value, data
            )

            # Different states may CREATE a different set of accounts. Accounts
            # that were crated by a human have the same address in all states.
            # This diverges from the yellow paper but at least we check that we
            # are not trying to create an already used address here
            if sort == "CREATE":
                if address in world.accounts:
                    # Address already used
                    raise EthereumError(
                        "This is bad. Same address is used for different contracts in different states"
                    )

            state.platform.start_transaction(
                sort=sort,
                address=address_migrated,
                price=price,
                data=data_migrated,
                caller=caller_migrated,
                value=value_migrated,
                gas=gaslimit,
            )

        # run over potentially several states and
        # generating potentially several others
        self.run()

        return address

    def preconstraint_for_call_transaction(
        self,
        address: Union[int, EVMAccount],
        data: Array,
        value: Optional[Union[int, Expression]] = None,
        contract_metadata: Optional[SolidityMetadata] = None,
    ) -> BoolOperation:
        """ Returns a constraint that excludes combinations of value and data that would cause an exception in the EVM
            contract dispatcher.
            :param address: address of the contract to call
            :param value: balance to be transferred (optional)
            :param data: symbolic transaction data
            :param contract_metadata: SolidityMetadata for the contract (optional)
        """
        if isinstance(address, EVMAccount):
            address = int(address)
        if not isinstance(address, int):
            raise TypeError("invalid address type")

        if not issymbolic(data):
            raise TypeError("data must be a symbolic array")

        if contract_metadata is None:
            contract_metadata = self.metadata.get(address)
            if contract_metadata is None:
                raise TypeError("no Solidity metadata available for the contract address")

        selectors = contract_metadata.function_selectors
        if not selectors or len(data) <= 4:
            return BoolConstant(True)

        symbolic_selector = data[:4]

        value_is_symbolic = issymbolic(value)

        constraint = None
        for selector in selectors:
            c = symbolic_selector == selector
            if value_is_symbolic and not contract_metadata.get_abi(selector)["payable"]:
                c = Operators.AND(c, value == 0)
            if constraint is None:
                constraint = c
            else:
                constraint = Operators.OR(constraint, c)

        return constraint

    def multi_tx_analysis(
        self,
        solidity_filename,
        working_dir=None,
        contract_name=None,
        tx_limit=None,
        tx_use_coverage=True,
        tx_send_ether=True,
        tx_account="attacker",
        tx_preconstrain=False,
        args=None,
    ):
        owner_account = self.create_account(balance=1000, name="owner")
        attacker_account = self.create_account(balance=1000, name="attacker")
        # Pretty print
        logger.info("Starting symbolic create contract")

        with open(solidity_filename) as f:
            contract_account = self.solidity_create_contract(
                f,
                contract_name=contract_name,
                owner=owner_account,
                args=args,
                working_dir=working_dir,
            )

        if tx_account == "attacker":
            tx_account = [attacker_account]
        elif tx_account == "owner":
            tx_account = [owner_account]
        elif tx_account == "combo1":
            tx_account = [owner_account, attacker_account]
        else:
            self.kill()
            raise EthereumError(
                'The account to perform the symbolic exploration of the contract should be "attacker", "owner" or "combo1"'
            )

        if contract_account is None:
            logger.info("Failed to create contract: exception in constructor")
            return
        prev_coverage = 0
        current_coverage = 0
        tx_no = 0
        while (current_coverage < 100 or not tx_use_coverage) and not self.is_killed():
            try:
                logger.info("Starting symbolic transaction: %d", tx_no)

                # run_symbolic_tx
                symbolic_data = self.make_symbolic_buffer(320)
                if tx_send_ether:
                    value = self.make_symbolic_value()
                else:
                    value = 0

                if tx_preconstrain:
                    self.constrain(
                        self.preconstraint_for_call_transaction(
                            address=contract_account, data=symbolic_data, value=value
                        )
                    )
                self.transaction(
                    caller=tx_account[min(tx_no, len(tx_account) - 1)],
                    address=contract_account,
                    data=symbolic_data,
                    value=value,
                )

                logger.info(
                    "%d alive states, %d terminated states",
                    self.count_ready_states(),
                    self.count_terminated_states(),
                )
            except NoAliveStates:
                break

            # Check if the maximum number of tx was reached
            if tx_limit is not None and tx_no + 1 == tx_limit:
                break

            # Check if coverage has improved or not
            if tx_use_coverage:
                prev_coverage = current_coverage
                current_coverage = self.global_coverage(contract_account)
                found_new_coverage = prev_coverage < current_coverage

                if not found_new_coverage:
                    break

            tx_no += 1

    def run(self, **kwargs):
        # Ethereum can have several sequential runs each for a different human
        # transaction. Each human transaction post a tx over all READY states.
        # Some states will end in a REVERT or a failed TX ultimatelly changing
        # very little state. Only the gas spent (and perhaps the nonce) will change
        # in the state after the attempted and failed tx. These states are not
        # considered for exploration in the next human tx/run

        # To differentiate the terminated sucessful terminated states from the
        # reverted (or not very interesting) ManticoreEVM uses another list:
        # saved_states
        # At the begining of a human tx/run it should not be any saved state
        with self.locked_context("ethereum.saved_states", list) as saved_states:
            if saved_states:
                raise Exception("ethereum.saved_states should be empty")

        # Every state.world has its pending_transaction filled. The run will
        # process it and potentially generate several READY and.or TERMINATED states.
        super().run(**kwargs)

        # The run may have finished be timeout/cancel or by state exhaustion
        # At this point we potentially have some READY states and some TERMINATED states
        # No busy states though

        # If there are ready states still then it was a paused execution
        assert not self._ready_states
        assert not self._busy_states
        assert not self.is_running()

        # ManticoreEthereum decided at terminate_state_callback wich state is
        # ready for next run and saved them at the context item
        # 'ethereum.saved_states'
        # Move successfully terminated states to ready states
        with self.locked_context("ethereum.saved_states", list) as saved_states:
            while saved_states:
                state_id = saved_states.pop()
                self._terminated_states.remove(state_id)
                self._ready_states.append(state_id)

    # Callbacks
    def _on_symbolic_sha3_callback(self, state, data, known_hashes):
        """ INTERNAL USE """
        assert issymbolic(data), "Data should be symbolic here!"
        with self.locked_context("ethereum") as context:
            known_sha3 = context.get("_known_sha3", None)
            if known_sha3 is None:
                known_sha3 = set()

            sha3_states = context.get("_sha3_states", [])
            results = []
            # If know_hashes is true then there is a _known_ solution for the hash
            known_hashes_cond = False
            for key, value in known_sha3:
                assert not issymbolic(key), "Saved sha3 data,hash pairs should be concrete"
                cond = key == data
                # TODO consider disabling this solver query.
                if not state.can_be_true(cond):
                    continue
                results.append((key, value))
                known_hashes_cond = Operators.OR(cond, known_hashes_cond)

            # adding a single random example so we can explore further
            if not results or state.can_be_true(known_hashes_cond == False):
                with state as temp:
                    temp.constrain(known_hashes_cond == False)
                    data_concrete = temp.solve_one(data)
                # data_concrete = state.solve_one(data)
                data_hash = int(sha3.keccak_256(data_concrete).hexdigest(), 16)
                results.append((data_concrete, data_hash))
                known_hashes_cond = Operators.OR(data_concrete == data, known_hashes_cond)
                known_sha3.add((data_concrete, data_hash))

            not_known_hashes_cond = Operators.NOT(known_hashes_cond)

            # We need to fork/save the state
            #################################
            # save the state to secondary storage
            # Build and enqueue a state for each solution
            with state as temp_state:
                if temp_state.can_be_true(not_known_hashes_cond):
                    temp_state.constrain(not_known_hashes_cond)
                    state_id = self._workspace.save_state(temp_state)
                    sha3_states[state_id] = [hsh for buf, hsh in known_sha3]
            context["_sha3_states"] = sha3_states
            context["_known_sha3"] = known_sha3

            if not state.can_be_true(known_hashes_cond):
                raise TerminateState("There is no matching sha3 pair, bailing out")
            state.constrain(known_hashes_cond)

            # send known hashes to evm
            known_hashes.update(results)

    def _on_concrete_sha3_callback(self, state, buf, value):
        """ INTERNAL USE """
        with self.locked_context("ethereum", dict) as ethereum_context:
            known_sha3 = ethereum_context.get("_known_sha3", None)
            if known_sha3 is None:
                known_sha3 = set()
            known_sha3.add((buf, value))
            ethereum_context["_known_sha3"] = known_sha3

    def _terminate_state_callback(self, state, e):
        """ INTERNAL USE
            Every time a state finishes executing the last transaction, we save it in
            our private list
        """
        if isinstance(e, AbandonState):
            # do nothing
            return
        world = state.platform

        state.context["last_exception"] = e
        e.testcase = False  # Do not generate a testcase file

        if not world.all_transactions:
            logger.debug("Something went wrong: search terminated in the middle of an ongoing tx")
            return

        tx = world.all_transactions[-1]

        # we initiated the Tx; we need process the outcome for now.
        # Fixme incomplete.
        if tx.is_human:
            if tx.sort == "CREATE":
                if tx.result == "RETURN":
                    world.set_code(tx.address, tx.return_data)
                else:
                    world.delete_account(tx.address)
        else:
            logger.info(
                "Manticore exception: state should be terminated only at the end of the human transaction"
            )

        # Human tx that ends in this wont modify the storage so finalize and
        # generate a testcase. FIXME This should be configurable as REVERT and
        # THROW; it actually changes the balance and nonce? of some accounts

        if tx.result in {"SELFDESTRUCT", "REVERT", "THROW", "TXERROR"}:
            pass
        elif tx.result in {"RETURN", "STOP"}:
            # if not a revert, we save the state for further transactions
            with self.locked_context("ethereum.saved_states", list) as saved_states:
                saved_states.append(state.id)

        else:
            logger.debug("Exception in state. Discarding it")

    # Callbacks
    def _did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
        """ INTERNAL USE """
        # logger.debug("%s", state.platform.current_vm)
        # TODO move to a plugin
        at_init = state.platform.current_transaction.sort == "CREATE"
        coverage_context_name = "evm.coverage"
        with self.locked_context(coverage_context_name, list) as coverage:
            if (state.platform.current_vm.address, instruction.pc, at_init) not in coverage:
                coverage.append((state.platform.current_vm.address, instruction.pc, at_init))

        state.context.setdefault("evm.trace", []).append(
            (state.platform.current_vm.address, instruction.pc, at_init)
        )

    def _did_evm_read_code(self, state, offset, size):
        """ INTERNAL USE """
        with self.locked_context("code_data", set) as code_data:
            for i in range(offset, offset + size):
                code_data.add((state.platform.current_vm.address, i))

    def get_metadata(self, address) -> Optional[SolidityMetadata]:
        """ Gets the solidity metadata for address.
            This is available only if address is a contract created from solidity
        """
        return self.metadata.get(int(address))

    def register_detector(self, d):
        """
        Unregisters a plugin. This will invoke detector's `on_unregister` callback.
        Shall be called after `.finalize`.
        """
        if not isinstance(d, Detector):
            raise EthereumError("Not a Detector")
        if d.name in self.detectors:
            raise EthereumError("Detector already registered")
        self.detectors[d.name] = d
        self.register_plugin(d)
        return d.name

    def unregister_detector(self, d):
        """
        Unregisters a detector. This will invoke detector's `on_unregister` callback.
        Shall be called after `.finalize` - otherwise, finalize won't add detector's finding to `global.findings`.
        """
        if not isinstance(d, (Detector, str)):
            raise EthereumError("Not a Detector")
        name = d
        if isinstance(d, Detector):
            name = d.name
        if name not in self.detectors:
            raise EthereumError("Detector not registered")
        d = self.detectors[name]
        del self.detectors[name]
        self.unregister_plugin(d)

    @property
    def workspace(self):
        return self._workspace._store.uri

    def current_location(self, state):
        world = state.platform
        address = world.current_vm.address
        pc = world.current_vm.pc
        at_init = world.current_transaction.sort == "CREATE"
        output = io.StringIO()
        write_findings(output, "", address, pc, at_init)
        md = self.get_metadata(address)
        if md is not None:
            src = md.get_source_for(pc, runtime=not at_init)
            output.write("Snippet:\n")
            output.write(src.replace("\n", "\n  ").strip())
            output.write("\n")
        return output.getvalue()

    def generate_testcase(self, state, message="", only_if=None, name="user"):
        """
        Generate a testcase to the workspace for the given program state. The details of what
        a testcase is depends on the type of Platform the state is, but involves serializing the state,
        and generating an input (concretizing symbolic variables) to trigger this state.

        The only_if parameter should be a symbolic expression. If this argument is provided, and the expression
        *can be true* in this state, a testcase is generated such that the expression will be true in the state.
        If it *is impossible* for the expression to be true in the state, a testcase is not generated.

        This is useful for conveniently checking a particular invariant in a state, and generating a testcase if
        the invariant can be violated.

        For example, invariant: "balance" must not be 0. We can check if this can be violated and generate a
        testcase::

            m.generate_testcase(state, 'balance CAN be 0', only_if=balance == 0)
            # testcase generated with an input that will violate invariant (make balance == 0)

        :param manticore.core.state.State state:
        :param str message: longer description of the testcase condition
        :param manticore.core.smtlib.Bool only_if: only if this expr can be true, generate testcase. if is None, generate testcase unconditionally.
        :param str name: short string used as the prefix for the workspace key (e.g. filename prefix for testcase files)
        :return: If a testcase was generated
        :rtype: bool
        """
        """
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        """
        if only_if is not None:
            with state as temp_state:
                temp_state.constrain(only_if)
                if temp_state.is_feasible():
                    return self.generate_testcase(temp_state, message, only_if=None, name=name)
                else:
                    return False

        blockchain = state.platform

        # FIXME. workspace should not be responsible for formating the output
        # each object knows its secrets, and each class should be able to report
        # its final state
        testcase = super().generate_testcase(
            state, message + f"({len(blockchain.human_transactions)} txs)", name=name
        )
        # TODO(mark): Refactor ManticoreOutput to let the platform be more in control
        #  so this function can be fully ported to EVMWorld.generate_workspace_files.

        local_findings = set()
        for detector in self.detectors.values():
            for address, pc, finding, at_init, constraint in detector.get_findings(state):
                if (address, pc, finding, at_init) not in local_findings:
                    local_findings.add((address, pc, finding, at_init, constraint))

        if len(local_findings):
            with testcase.open_stream("findings") as findings:
                for address, pc, finding, at_init, constraint in local_findings:
                    findings.write("- %s -\n" % finding)
                    write_findings(findings, "  ", address, pc, at_init)
                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc, runtime=not at_init)
                        findings.write("  Snippet:\n")
                        findings.write(src.replace("\n", "\n    ").strip())
                        findings.write("\n")

        with testcase.open_stream("summary") as stream:
            is_something_symbolic = state.platform.dump(stream, state, self, message)

            with self.locked_context("ethereum") as context:
                known_sha3 = context.get("_known_sha3", None)
                if known_sha3:
                    stream.write("Known hashes:\n")
                    for key, value in known_sha3:
                        stream.write("%s::%x\n" % (binascii.hexlify(key), value))

            if is_something_symbolic:
                stream.write(
                    "\n\n(*) Example solution given. Value is symbolic and may take other values\n"
                )

        # Transactions

        with testcase.open_stream("tx") as tx_summary:
            with testcase.open_stream("tx.json") as txjson:
                txlist = []
                is_something_symbolic = False

                for sym_tx in blockchain.human_transactions:  # external transactions
                    tx_summary.write(
                        "Transactions No. %d\n" % blockchain.transactions.index(sym_tx)
                    )

                    conc_tx = sym_tx.concretize(state)
                    txlist.append(conc_tx.to_dict(self))

                    is_something_symbolic = sym_tx.dump(tx_summary, state, self, conc_tx=conc_tx)

                if is_something_symbolic:
                    tx_summary.write(
                        "\n\n(*) Example solution given. Value is symbolic and may take other values\n"
                    )

                json.dump(txlist, txjson)

        # logs
        with testcase.open_stream("logs") as logs_summary:
            is_something_symbolic = False
            for log_item in blockchain.logs:
                is_log_symbolic = issymbolic(log_item.memlog)
                is_something_symbolic = is_log_symbolic or is_something_symbolic
                solved_memlog = state.solve_one(log_item.memlog)
                printable_bytes = "".join(
                    [c for c in map(chr, solved_memlog) if c in string.printable]
                )

                logs_summary.write("Address: %x\n" % log_item.address)
                logs_summary.write(
                    "Memlog: %s (%s) %s\n"
                    % (
                        binascii.hexlify(solved_memlog).decode(),
                        printable_bytes,
                        flagged(is_log_symbolic),
                    )
                )
                logs_summary.write("Topics:\n")
                for i, topic in enumerate(log_item.topics):
                    logs_summary.write(
                        "\t%d) %x %s" % (i, state.solve_one(topic), flagged(issymbolic(topic)))
                    )

        with testcase.open_stream("constraints") as smt_summary:
            smt_summary.write(str(state.constraints))

        trace = state.context.get("evm.trace")
        if trace:
            with testcase.open_stream("trace") as f:
                self._emit_trace_file(f, trace)
        return testcase

    @staticmethod
    def _emit_trace_file(filestream, trace):
        """
        :param filestream: file object for the workspace trace file
        :param trace: list of (contract address, pc) tuples
        :type trace: list[tuple(int, int)]
        """
        for contract, pc, at_init in trace:
            if pc == 0:
                filestream.write("---\n")
            ln = "0x{:x}:0x{:x} {}\n".format(contract, pc, "*" if at_init else "")
            filestream.write(ln)

    @property
    def global_findings(self):
        global_findings = set()
        for detector in self.detectors.values():
            for address, pc, finding, at_init in detector.global_findings:
                if (address, pc, finding, at_init) not in global_findings:
                    global_findings.add((address, pc, finding, at_init))
        return global_findings

    @ManticoreBase.at_not_running
    def finalize(self, procs=10):
        """
        Terminate and generate testcases for all currently alive states (contract
        states that cleanly executed to a STOP or RETURN in the last symbolic
        transaction).

        :param procs: nomber of local processes to use in the reporting generation
        """

        logger.debug("Finalizing %d states.", self.count_states())

        def finalizer(state_id):
            st = self._load(state_id)
            logger.debug("Generating testcase for state_id %d", state_id)
            last_tx = st.platform.last_transaction
            message = last_tx.result if last_tx else "NO STATE RESULT (?)"
            self.generate_testcase(st, message=message)

        def worker_finalize(q):
            try:
                while True:
                    finalizer(q.get_nowait())
            except EmptyQueue:
                pass

        q = Queue()
        for state_id in self._all_states:
            # we need to remove -1 state before forking because it may be in memory
            q.put(state_id)

        report_workers = [Process(target=worker_finalize, args=(q,)) for _ in range(procs)]
        for proc in report_workers:
            proc.start()

        for proc in report_workers:
            proc.join()

        # global summary
        with self._output.save_stream("global.findings") as global_findings_stream:
            for address, pc, finding, at_init in self.global_findings:
                global_findings_stream.write("- %s -\n" % finding)
                write_findings(global_findings_stream, "  ", address, pc, at_init)
                md = self.get_metadata(address)
                if md is not None:
                    source_code_snippet = md.get_source_for(pc, runtime=not at_init)
                    global_findings_stream.write("  Solidity snippet:\n")
                    global_findings_stream.write("    ".join(source_code_snippet.splitlines(True)))
                    global_findings_stream.write("\n")

        self.save_run_data()

        with self._output.save_stream("global.summary") as global_summary:
            # (accounts created by contract code are not in this list )
            global_summary.write("Global runtime coverage:\n")
            for address in self.contract_accounts.values():
                global_summary.write(
                    "{:x}: {:2.2f}%\n".format(int(address), self.global_coverage(address))
                )

                md = self.get_metadata(address)
                if md is not None and len(md.warnings) > 0:
                    global_summary.write("\n\nCompiler warnings for %s:\n" % md.name)
                    global_summary.write(md.warnings)

        for address, md in self.metadata.items():
            with self._output.save_stream("global_%s.sol" % md.name) as global_src:
                global_src.write(md.source_code)
            with self._output.save_stream(
                "global_%s_runtime.bytecode" % md.name, binary=True
            ) as global_runtime_bytecode:
                global_runtime_bytecode.write(md.runtime_bytecode)
            with self._output.save_stream(
                "global_%s_init.bytecode" % md.name, binary=True
            ) as global_init_bytecode:
                global_init_bytecode.write(md.init_bytecode)

            with self._output.save_stream(
                "global_%s.runtime_asm" % md.name
            ) as global_runtime_asm, self.locked_context("runtime_coverage") as seen:

                runtime_bytecode = md.runtime_bytecode
                count, total = 0, 0
                for i in EVMAsm.disassemble_all(runtime_bytecode):
                    if (address, i.pc) in seen:
                        count += 1
                        global_runtime_asm.write("*")
                    else:
                        global_runtime_asm.write(" ")

                    global_runtime_asm.write("%4x: %s\n" % (i.pc, i))
                    total += 1

            with self._output.save_stream(
                "global_%s.init_asm" % md.name
            ) as global_init_asm, self.locked_context("init_coverage") as seen:
                count, total = 0, 0
                for i in EVMAsm.disassemble_all(md.init_bytecode):
                    if (address, i.pc) in seen:
                        count += 1
                        global_init_asm.write("*")
                    else:
                        global_init_asm.write(" ")

                    global_init_asm.write("%4x: %s\n" % (i.pc, i))
                    total += 1

            with self._output.save_stream(
                "global_%s.init_visited" % md.name
            ) as f, self.locked_context("init_coverage") as seen:
                visited = set((o for (a, o) in seen if a == address))
                for o in sorted(visited):
                    f.write("0x%x\n" % o)

            with self._output.save_stream(
                "global_%s.runtime_visited" % md.name
            ) as f, self.locked_context("runtime_coverage") as seen:
                visited = set()
                for (a, o) in seen:
                    if a == address:
                        visited.add(o)
                for o in sorted(visited):
                    f.write("0x%x\n" % o)

        self.remove_all()

    def global_coverage(self, account):
        """ Returns code coverage for the contract on `account_address`.
            This sums up all the visited code lines from any of the explored
            states.
        """
        account_address = int(account)
        runtime_bytecode = None
        # Search one state in which the account_address exists
        for state in self.all_states:
            world = state.platform
            if account_address in world:
                code = world.get_code(account_address)
                runtime_bytecode = state.solve_one(code)
                break
        else:
            return 0.0
        with self.locked_context("evm.coverage") as coverage:
            seen = {off for addr, off, init in coverage if addr == account_address and not init}
        return calculate_coverage(runtime_bytecode, seen)
