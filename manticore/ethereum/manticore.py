import binascii
import json
import logging
from multiprocessing import Queue, Process
from queue import Empty as EmptyQueue
from typing import Dict, Optional, Union
import io
import pyevmasm as EVMAsm
import random
import tempfile
import time

from crytic_compile import CryticCompile, InvalidCompilation, is_supported

from ..core.manticore import ManticoreBase, ManticoreError

from ..core.smtlib import (
    ConstraintSet,
    Array,
    ArrayProxy,
    BitVec,
    Operators,
    BoolConstant,
    Expression,
    issymbolic,
    SelectedSolver,
)
from ..core.state import AbandonState
from .account import EVMContract, EVMAccount, ABI
from .detectors import Detector
from .solidity import SolidityMetadata
from .state import State
from ..exceptions import EthereumError, DependencyError, NoAliveStates
from ..platforms import evm
from ..utils import config
from ..utils.deprecated import deprecated
from ..utils.enums import Sha3Type
from ..utils.helpers import PickleSerializer, printable_bytes

logger = logging.getLogger(__name__)
logging.getLogger("CryticCompile").setLevel(logging.ERROR)

consts = config.get_group("evm")
consts.add("defaultgas", 3000000, "Default gas value for ethereum transactions.")
consts.add(
    "sha3",
    default=Sha3Type.symbolicate,
    description="concretize: sound simple concretization\nsymbolicate(*): unsound symbolication with an out of cycle false positive killing\nfake: let the solver choose a function to emulate some of the hash characteristics (This potentially produces wrong testcases) ",
)
consts.add(
    "sha3timeout",
    60 * 60,
    "Default timeout for matching sha3 for unsound states (see unsound symbolication).",
)


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
    """Manticore EVM manager

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

    _published_events = {"solve"}

    def make_symbolic_buffer(self, size, name=None, avoid_collisions=False):
        """Creates a symbolic buffer of size bytes to be used in transactions.
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
        """Creates a symbolic value, normally a uint256, to be used in transactions.
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
            name = "SVALUE"
            avoid_collisions = True
        return self.constraints.new_bitvec(nbits, name=name, avoid_collisions=avoid_collisions)

    def make_symbolic_address(self, *accounts, name=None, select="both"):
        """
        Creates a symbolic address and constrains it to pre-existing addresses or the 0 address.

        :param name: Name of the symbolic variable. Defaults to 'TXADDR' and later to 'TXADDR_<number>'
        :param select: Whether to select contracts or normal accounts. Not implemented for now.
        :return: Symbolic address in form of a BitVecVariable.
        """
        if select not in ("both", "normal", "contract"):
            raise EthereumError("Wrong selection type")
        # if select in ("normal", "contract"):
        # FIXME need to select contracts or normal accounts
        #    raise NotImplemented
        if not accounts:
            accounts = self._accounts.values()
        avoid_collisions = False
        if name is None:
            name = "TXADDR"
            avoid_collisions = True

        symbolic_address = self.constraints.new_bitvec(
            160, name=name, avoid_collisions=avoid_collisions
        )

        constraint = symbolic_address == 0
        for account in accounts:
            if select == "contract" and not self.get_code(account):
                continue
            if select == "normal" and self.get_code(account):
                continue
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
    def _compile_through_crytic_compile(filename, contract_name, libraries, crytic_compile_args):
        """
        :param filename: filename to compile
        :param contract_name: contract to extract
        :param libraries: an itemizable of pairs (library_name, address)
        :param crytic_compile_args: crytic compile options (https://github.com/crytic/crytic-compile/wiki/Configuration)
        :type crytic_compile_args: dict
        :return:
        """
        try:

            if crytic_compile_args:
                crytic_compile = CryticCompile(filename, **crytic_compile_args)
            else:
                crytic_compile = CryticCompile(filename)

            if not contract_name:
                if len(crytic_compile.contracts_names_without_libraries) > 1:
                    raise EthereumError(
                        f"Solidity file must contain exactly one contract or you must select one. Contracts found: {', '.join(crytic_compile.contracts_names)}"
                    )
                contract_name = list(crytic_compile.contracts_names_without_libraries)[0]

            if contract_name not in crytic_compile.contracts_names:
                raise ValueError(f"Specified contract not found: {contract_name}")

            name = contract_name

            libs = crytic_compile.libraries_names(name)
            if libraries:
                libs = [l for l in libs if l not in libraries]
            if libs:
                raise DependencyError(libs)

            bytecode = bytes.fromhex(crytic_compile.bytecode_init(name, libraries))
            runtime = bytes.fromhex(crytic_compile.bytecode_runtime(name, libraries))
            srcmap = crytic_compile.srcmap_init(name)
            srcmap_runtime = crytic_compile.srcmap_runtime(name)
            hashes = crytic_compile.hashes(name)
            abi = crytic_compile.abi(name)

            filename = crytic_compile.filename_of_contract(name).absolute
            with open(filename) as f:
                source_code = f.read()

            return name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi

        except InvalidCompilation as e:
            raise EthereumError(
                f"Errors : {e}\n. Solidity failed to generate bytecode for your contract. Check if all the abstract functions are implemented. "
            )

    @staticmethod
    def _compile(source_code, contract_name, libraries=None, crytic_compile_args=None):
        """Compile a Solidity contract, used internally

        :param source_code: solidity source
        :type source_code: string (filename, directory, etherscan address) or a file handle
        :param contract_name: a string with the name of the contract to analyze
        :param libraries: an itemizable of pairs (library_name, address)
        :param crytic_compile_args: crytic compile options (https://github.com/crytic/crytic-compile/wiki/Configuration)
        :type crytic_compile_args: dict
        :return: name, source_code, bytecode, srcmap, srcmap_runtime, hashes
        :return: name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings
        """

        crytic_compile_args = dict() if crytic_compile_args is None else crytic_compile_args

        if isinstance(source_code, io.IOBase):
            source_code = source_code.name

        if (
            isinstance(source_code, str)
            and not is_supported(source_code)
            and
            # Until https://github.com/crytic/crytic-compile/issues/103 is implemented
            "ignore_compile" not in crytic_compile_args
        ):
            with tempfile.NamedTemporaryFile("w+", suffix=".sol") as temp:
                temp.write(source_code)
                temp.flush()
                compilation_result = ManticoreEVM._compile_through_crytic_compile(
                    temp.name, contract_name, libraries, crytic_compile_args
                )
        else:
            compilation_result = ManticoreEVM._compile_through_crytic_compile(
                source_code, contract_name, libraries, crytic_compile_args
            )

        (
            name,
            source_code,
            bytecode,
            runtime,
            srcmap,
            srcmap_runtime,
            hashes,
            abi,
        ) = compilation_result
        warnings = ""

        return (name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings)

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

    def __init__(self, plugins=None, **kwargs):
        """
        A Manticore EVM manager
        :param plugins: the plugins to register in this manticore manager
        """
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        super().__init__(initial_state, **kwargs)
        if plugins is not None:
            for p in plugins:
                self.register_plugin(p)
        self.subscribe("will_terminate_state", self._terminate_state_callback)
        self.subscribe("did_evm_execute_instruction", self._did_evm_execute_instruction_callback)
        if consts.sha3 is consts.sha3.concretize:
            self.subscribe("on_symbolic_function", self._on_concretize)
        elif consts.sha3 is consts.sha3.symbolicate:
            self.subscribe("on_symbolic_function", self._on_unsound_symbolication)
        elif consts.sha3 is consts.sha3.fake:
            self.subscribe("on_symbolic_function", self._on_unsound_symbolication)

        self._accounts: Dict[str, EVMContract] = dict()
        self._serializer = PickleSerializer()

        self.constraints = constraints
        self.detectors: Dict[str, Detector] = {}
        self.metadata: Dict[int, SolidityMetadata] = {}

    @property
    def world(self):
        """ The world instance or None if there is more than one state """
        return self.get_world()

    # deprecate this 5 in favor of for state in m.all_states: do stuff?
    @property  # type: ignore
    @deprecated("You should iterate over `m.all_states` instead.")
    def completed_transactions(self):
        with self.locked_context("ethereum") as context:
            return context["_completed_transactions"]

    @deprecated("You should use the `platform` member of a `state` instance instead.")
    def get_world(self, state_id=None):
        """ Returns the evm world of `state_id` state. """
        if state_id is None:
            state_id = self._ready_states[0]

        state = self._load(state_id)
        if state is None:
            return None
        else:
            return state.platform

    @deprecated("Instead, call `get_balance` on a state instance")
    def get_balance(self, address, state_id=None):
        """ Balance for account `address` on state `state_id` """
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_balance(address)

    @deprecated("Instead, call `get_storage_data` on a state instance")
    def get_storage_data(self, address, offset, state_id=None):
        """ Storage data for `offset` on account `address` on state `state_id` """
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_storage_data(address, offset)

    @deprecated("Instead, call `get_code` on a state instance")
    def get_code(self, address, state_id=None):
        """ Storage data for `offset` on account `address` on state `state_id` """
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_code(address)

    @deprecated("Instead, use `state.last_transaction.return_data` on a state instance")
    def last_return(self, state_id=None):
        """ Last returned buffer for state `state_id` """
        state = self.load(state_id)
        return state.platform.last_transaction.return_data

    @deprecated("Instead, use `state.transactions` on a state instance")
    def transactions(self, state_id=None):
        """ Transactions list for state `state_id` """
        state = self._load(state_id)
        return state.platform.transactions

    @deprecated("Instead, use `state.transactions` on a state instance")
    def human_transactions(self, state_id=None):
        """ Transactions list for state `state_id` """
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
            raise NotImplementedError(f"Could not produce symbolic argument of type {ty[0]}")

        return result

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
        gas=None,
        compile_args=None,
    ):
        """Creates a solidity contract and library dependencies

        :param source_code: solidity source code
        :type source_code: string (filename, directory, etherscan address) or a file handle
        :param owner: owner account (will be default caller in any transactions)
        :type owner: int or EVMAccount
        :param contract_name: Name of the contract to analyze (optional if there is a single one in the source code)
        :type contract_name: str
        :param balance: balance to be transferred on creation
        :type balance: int or BitVecVariable
        :param address: the address for the new contract (optional)
        :type address: int or EVMAccount
        :param tuple args: constructor arguments
        :param compile_args: crytic compile options #FIXME(https://github.com/crytic/crytic-compile/wiki/Configuration)
        :type compile_args: dict
        :param gas: gas budget for each contract creation needed (may be more than one if several related contracts defined in the solidity source)
        :type gas: int
        :rtype: EVMAccount
        """
        if compile_args is None:
            compile_args = dict()

        if libraries is None:
            deps = {}
        else:
            deps = dict(libraries)

        contract_names = [contract_name]
        while contract_names:
            contract_name_i = contract_names.pop()
            try:
                compile_results = self._compile(
                    source_code, contract_name_i, libraries=deps, crytic_compile_args=compile_args
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
                    # Balance could be symbolic, lets ask the solver
                    # Option 1: balance can not be 0 and the function is marked as not payable
                    maybe_balance = balance == 0
                    self._publish(
                        "will_solve", None, self.constraints, maybe_balance, "can_be_true"
                    )
                    must_have_balance = SelectedSolver.instance().can_be_true(
                        self.constraints, maybe_balance
                    )
                    self._publish(
                        "did_solve",
                        None,
                        self.constraints,
                        maybe_balance,
                        "can_be_true",
                        must_have_balance,
                    )
                    if not must_have_balance:
                        # balance always != 0
                        if not md.constructor_abi["payable"]:
                            raise EthereumError(
                                f"Can't create solidity contract with balance ({balance}) "
                                f"different than 0 because the contract's constructor is not payable."
                            )

                    for state in self.ready_states:
                        world = state.platform

                        expr = Operators.UGE(world.get_balance(owner.address), balance)
                        self._publish("will_solve", None, self.constraints, expr, "can_be_true")
                        sufficient = SelectedSolver.instance().can_be_true(
                            self.constraints,
                            expr,
                        )
                        self._publish(
                            "did_solve", None, self.constraints, expr, "can_be_true", sufficient
                        )

                        if not sufficient:
                            raise EthereumError(
                                f"Can't create solidity contract with balance ({balance}) "
                                f"because the owner account ({owner}) has insufficient balance."
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
                    contract_account = self.create_contract(
                        owner=owner, init=md._init_bytecode, balance=0, gas=gas
                    )
                if contract_account is None:
                    return None

                self.metadata[int(contract_account)] = md

                deps[contract_name_i] = int(contract_account)
            except DependencyError as e:
                contract_names.append(contract_name_i)
                for lib_name in e.lib_names:
                    if lib_name not in deps:
                        contract_names.append(lib_name)
            except EthereumError as e:
                logger.info(f"Failed to build contract {contract_name_i} {str(e)}")
                self.kill()
                raise

        # If the contract was created successfully in at least 1 state return account
        for state in self.ready_states:
            if state.platform.get_code(int(contract_account)):
                return contract_account

        logger.info("Failed to compile contract %r", contract_names)

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
        """Creates a contract

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

        self._transaction("CREATE", owner, balance, address, data=init, gas=gas)
        # TODO detect failure in the constructor
        if self.count_ready_states():
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

    def start_block(
        self, blocknumber=None, timestamp=None, difficulty=0, gaslimit=0, coinbase=None
    ):
        for state in self.ready_states:
            world = state.platform
            world.start_block(
                blocknumber=blocknumber,
                timestamp=timestamp,
                difficulty=difficulty,
                gaslimit=gaslimit,
                coinbase=coinbase,
            )

    def end_block(self):
        for state in self.ready_states:
            world = state.platform
            world.end_block()

    def transaction(self, caller, address, value, data, gas=None, price=1):
        """Issue a symbolic transaction in all running states

        :param caller: the address of the account sending the transaction
        :type caller: int or EVMAccount
        :param address: the address of the contract to call
        :type address: int or EVMAccount
        :param value: balance to be transfered on creation
        :type value: int or BitVecVariable
        :param data: initial data
        :param gas: gas budget
        :param price: gas unit price
        :raises NoAliveStates: if there are no alive states to execute
        """
        self._transaction(
            "CALL", caller, value=value, address=address, data=data, gas=gas, price=price
        )

    def create_account(self, balance=0, address=None, code=None, name=None, nonce=None):
        """Low level creates an account. This won't generate a transaction.

        :param balance: balance to be set on creation (optional)
        :type balance: int or BitVecVariable
        :param address: the address for the new account (optional)
        :type address: int
        :param code: the runtime code for the new account (None means normal account), str or bytes (optional)
        :param nonce: force a specific nonce
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
        if not isinstance(balance, (int, BitVec)):
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
            world.create_account(address, balance, code=code, storage=None, nonce=nonce)

        self._accounts[name] = EVMAccount(address, manticore=self, name=name)
        return self.accounts[name]

    def _migrate_tx_expressions(self, state, caller, address, value, data, gas, price):
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
                data = ArrayProxy(array=data)

        if issymbolic(gas):
            gas = state.migrate_expression(gas)

        if issymbolic(price):
            gas = state.migrate_expression(price)

        for c in global_constraints:
            state.constrain(c)

        return caller, address, value, data, gas, price

    def _transaction(self, sort, caller, value=0, address=None, data=None, gas=None, price=1):
        """Initiates a transaction

        :param caller: caller account
        :type caller: int or EVMAccount
        :param int address: the address for the transaction (optional)
        :param value: value to be transferred
        :param price: the price of gas for this transaction.
        :type value: int or BitVecVariable
        :param str data: initializing evm bytecode and arguments or transaction call data
        :param gas: gas budget for current transaction
        :rtype: EVMAccount
        """
        if gas is None:
            gas = consts.defaultgas
        # Type Forgiveness
        if isinstance(address, EVMAccount):
            address = int(address)
        if isinstance(caller, EVMAccount):
            caller = int(caller)
        # Defaults, call data is empty
        if data is None:
            data = b""
        if isinstance(data, str):
            data = bytes(data)
        if not isinstance(data, (bytes, Array)):
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
            (
                caller_migrated,
                address_migrated,
                value_migrated,
                data_migrated,
                gas_migrated,
                price_migrated,
            ) = self._migrate_tx_expressions(state, caller, address, value, data, gas, price)

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
                price=price_migrated,
                data=data_migrated,
                caller=caller_migrated,
                value=value_migrated,
                gas=gas_migrated,
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
    ):
        """Returns a constraint that excludes combinations of value and data that would cause an exception in the EVM
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
            return BoolConstant(value=True)

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
        contract_name=None,
        tx_limit=None,
        tx_use_coverage=True,
        tx_send_ether=True,
        tx_account="attacker",
        tx_preconstrain=False,
        args=None,
        compile_args=None,
    ):
        owner_account = self.create_account(balance=10 ** 10, name="owner")
        attacker_account = self.create_account(balance=10 ** 10, name="attacker")
        # Pretty print
        logger.info("Starting symbolic create contract")

        if tx_send_ether:
            create_value = self.make_symbolic_value()
        else:
            create_value = 0

        contract_account = self.solidity_create_contract(
            solidity_filename,
            contract_name=contract_name,
            owner=owner_account,
            args=args,
            compile_args=compile_args,
            balance=create_value,
            gas=230000,
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
                    gas=230000,
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
                raise EthereumError("ethereum.saved_states should be empty")

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

        # ManticoreEthereum decided at terminate_state_callback which state is
        # ready for next run and saved them at the context item
        # 'ethereum.saved_states'
        # Move successfully terminated states to ready states
        with self.locked_context("ethereum.saved_states", list) as saved_states:
            while saved_states:
                state_id = saved_states.pop()
                if state_id in self._terminated_states:
                    self._revive_state(state_id)

    # Callbacks
    def _on_concretize(self, state, func, data, result):
        if not issymbolic(data):
            y_concrete = func(data)
        else:
            with self.locked_context("ethereum", dict) as context:
                # adding a single random example so we can explore further
                x_concrete = state.solve_one(data)
                y_concrete = func(x_concrete)

                # Lets contraint the data to the single sound concretization
                state.constrain(x_concrete == data)

        result.append(y_concrete)

    def _on_unsound_symbolication(self, state, func, data, result):
        """Apply the function symbolic unfriendly func to data
        state: a manticore state
        func: a concrete normal python function like `sha3()`
        data: a concrete or symbolic value of the domain of func
        result: an empty list where to put the result


        This method returns a fresh free symbol Y representing all the potential
        results of applying func to data.
        The relations between the input and the output of funcis saved in an
        internal table. Effectively an uninstantiated Function.


        func(data)  -> result = constraints.new_bitvec()
                       symbolic_pairs.append((data, result))
                       constraints.add(func_table is injective)

        """
        name = func.__name__
        value = func(data)  # If func returns None then result should considered unknown/symbolic

        # Value is known. Let's add it to our concrete database
        if value is not None:
            with self.locked_context("ethereum", dict) as ethereum_context:
                global_known_pairs = ethereum_context.get(f"symbolic_func_conc_{name}", set())
                if (data, value) not in global_known_pairs:
                    global_known_pairs.add((data, value))
                    ethereum_context[f"symbolic_func_conc_{name}"] = global_known_pairs
                    logger.info(f"Found a concrete {name} {data} -> {value}")
            concrete_pairs = state.context.get(f"symbolic_func_conc_{name}", set())
            concrete_pairs.add((data, value))
            state.context[f"symbolic_func_conc_{name}"] = concrete_pairs
        else:
            # we can not calculate the concrete value lets use a fresh symbol
            with self.locked_context("ethereum", dict) as ethereum_context:
                functions = ethereum_context.get("symbolic_func", dict())
                if name in functions and functions[name] != func:
                    logger.debug("Redefining symbolic function. Same name different functions")
                functions[name] = func
                ethereum_context["symbolic_func"] = functions

            # We are adding a new pair to the symbolic pairs
            # Reset the soundcheck if True
            if state.context.get("soundcheck", None) == True:
                state.context["soundcheck"] = None

            data_var = state.new_symbolic_buffer(len(data))  # FIXME: generalize to bitvec
            state.constrain(data_var == data)
            data = data_var

            # symbolic_pairs list of symbolic applications of func in sate
            symbolic_pairs = state.context.get(f"symbolic_func_sym_{name}", [])

            # lets make a fresh 256 bit symbol representing any potential hash
            value = state.new_symbolic_value(256)

            for x, y in symbolic_pairs:
                # if we found another pair that matches use that instead
                # the duplicated pair is not added to symbolic_pairs
                if state.must_be_true(Operators.OR(x == data, y == value)):
                    data, value = x, y
                    break
            else:
                # New pair
                # add basic conditions no-collisions; new pair is added to symbolic_pairs
                for x, y in symbolic_pairs:
                    if len(x) == len(data):
                        constraint = (x == data) == (y == value)
                    else:
                        constraint = y != value
                    state.constrain(constraint)
                symbolic_pairs.append((data, value))
            state.context[f"symbolic_func_sym_{name}"] = symbolic_pairs

        # let it return just new_hash
        result.append(value)

    def fix_unsound_symbolication_fake(self, state):
        """This method goes through all the applied symbolic functions and tries
        to find a concrete matching set of pairs
        """

        def make_cond(state, table):
            symbolic_pairs = state.context.get(f"symbolic_func_sym_{table}", ())
            # Make every result distant from each other
            for x, y in symbolic_pairs:
                state.constrain(Operators.EXTRACT(y, 0, 16) == 0)

        with self.locked_context("ethereum", dict) as ethereum_context:
            functions = ethereum_context.get("symbolic_func", list())
        for table in functions:
            make_cond(state, table)

        # Ok all functions had a match for current state
        return state.can_be_true(True)

    def fix_unsound_symbolication_sound(self, state):
        """This method goes through all the applied symbolic functions and tries
        to find a concrete matching set of pairs
        """

        def concretize_known_pairs(state, symbolic_pairs, known_pairs):
            # Each symbolic pair must match at least one of the concrete
            # pairs we know

            for xa, ya in symbolic_pairs:
                cond = False
                for xc, yc in known_pairs:
                    if len(xa) == len(xc):
                        cond = Operators.OR(Operators.AND(xa == xc, ya == yc), cond)
                state.constrain(cond)
                if cond is False:
                    return

        def match(state, func, symbolic_pairs, concrete_pairs, start=None):
            """Tries to find a concrete match for the symbolic pairs. It uses
            concrete_pairs (and potentially extends it with solved pairs) until
            a matching set of concrete pairs is found, or fail.

            state: the current state
            func: the relation between domain and range in symbolic_pairs/concrete_pairs
            symbolic_pairs: related symbolic values that need a set of solutions
            concrete_pairs: known of concrete pairs that may match some of the symbolic pairs


            """
            if time.time() - start > consts.sha3timeout:
                logger.info("Timeout on sound check for state %d", state.id)
                return False

            # The base case. No symbolic pairs. Just check if the state is feasible.
            if not symbolic_pairs:
                return state.can_be_true(True)

            if not state.can_be_true(True):
                return False

            for i in range(len(symbolic_pairs)):
                # shuffle and if it failed X times at some depth bail configurable
                x, y = symbolic_pairs[i]
                new_symbolic_pairs = symbolic_pairs[:i] + symbolic_pairs[i + 1 :]
                new_concrete_pairs = set(concrete_pairs)
                unseen = True  # Is added only unseen pairs could make it sat
                for x_concrete, y_concrete in concrete_pairs:
                    if len(x) == len(x_concrete):  # If the size of the buffer wont
                        # match it does not matter
                        unseen = Operators.AND(x != x_concrete, y != y_concrete, unseen)
                # Search for a new unseen sha3 pair
                with state as temp_state:
                    temp_state.constrain(unseen)
                    new_x_concretes = temp_state.solve_n(x, nsolves=1)
                    new_y_concretes = map(func, new_x_concretes)
                    new_concrete_pairs.update(zip(new_x_concretes, new_y_concretes))

                    """
                    Idea:
                    new_x_concretes = check_offline_db(temp_state.solve_n(y, nsolves=1))
                    new_y_concretes = map(func, new_x_concretes)
                    new_concrete_pairs.update(zip(new_x_concretes, new_y_concretes))
                    """

                # Consider all the new set of sha3 pairs and rebuild the seen condition
                seen = False
                for x_concrete, y_concrete in new_concrete_pairs:
                    if len(x) == len(x_concrete):  # If the size of the buffer wont
                        # match it does not matter
                        seen = Operators.OR(Operators.AND(x == x_concrete, y == y_concrete), seen)

                # With the current x,y pair being one of the known sha3 pairs try
                # to match the following symbolic pairs
                with state as temp_state:
                    temp_state.constrain(seen)
                    if match(temp_state, func, new_symbolic_pairs, new_concrete_pairs, start=start):
                        concrete_pairs.update(new_concrete_pairs)
                        return True
            return False

        with self.locked_context("ethereum", dict) as ethereum_context:
            functions = ethereum_context.get("symbolic_func", list())
            known_pairs_dict = {}
            for table in functions:
                known_pairs_dict[table] = ethereum_context.get(f"symbolic_func_conc_{table}", set())
        for table in functions:
            symbolic_pairs = state.context.get(f"symbolic_func_sym_{table}", ())

            known_pairs = known_pairs_dict[table]
            new_known_pairs = set(known_pairs)

            # Add concrete knowledge in
            for xa, ya in symbolic_pairs:
                for xc, yc in known_pairs:
                    state.constrain(Operators.OR(xa == xc, ya != yc))
                    state.constrain(Operators.OR(xa != xc, ya == yc))

            # Keep only pairs that have not yet been fixed to a single solution
            symbolic_pairs = [
                (xa, ya)
                for xa, ya in symbolic_pairs
                if len(state.solve_n(xa[0], nsolves=2)) != 1
                or len(state.solve_n(ya, nsolves=2)) != 1
            ]

            if not match(
                state, functions[table], symbolic_pairs, new_known_pairs, start=time.time()
            ):
                return False

            # Now paste the known pairs in the state constraints
            concretize_known_pairs(state, symbolic_pairs, new_known_pairs)
            state.context[f"symbolic_func_sym_{table}_done"] = symbolic_pairs

            # Share the concrete pairs with other states.
            # Depends on the order in which the states are processed
            # with self.locked_context("ethereum", dict) as ethereum_context:
            #    ethereum_context[f"symbolic_func_conc_{table}"] = new_known_pairs

        # Ok all functions had a match for current state
        return state.can_be_true(True)

    def fix_unsound_symbolication(self, state):
        soundcheck = state.context.get("soundcheck", None)
        if soundcheck is not None:
            return soundcheck
        if consts.sha3 is consts.sha3.symbolicate:
            state.context["soundcheck"] = self.fix_unsound_symbolication_sound(state)
        elif consts.sha3 is consts.sha3.fake:
            state.context["soundcheck"] = self.fix_unsound_symbolication_fake(state)
        else:
            state.context["soundcheck"] = True
        return state.context["soundcheck"]

    def _terminate_state_callback(self, state, e):
        """INTERNAL USE
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
        """
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
        """
        # Human tx that ends in this wont modify the storage so finalize and
        # generate a testcase. FIXME This should be configurable as REVERT and
        # THROW; it actually changes the balance and nonce? of some accounts

        if tx.return_value == 0:
            pass
        else:
            # if not a revert, we save the state for further transactions
            with self.locked_context("ethereum.saved_states", list) as saved_states:
                saved_states.append(state.id)

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

    def get_metadata(self, address) -> Optional[SolidityMetadata]:
        """Gets the solidity metadata for address.
        This is available only if address is a contract created from solidity
        """
        return self.metadata.get(address)

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

    @property
    def global_findings(self):
        try:
            return self._global_findings
        except AttributeError:
            raise Exception("You need to call finalize() first")

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
        The only_if parameter should be a symbolic expression. If this argument is provided, and the expression
        *can be true* in this state, a testcase is generated such that the expression will be true in the state.
        If it *is impossible* for the expression to be true in the state, a testcase is not generated.

        This is useful for conveniently checking a particular invariant in a state, and generating a testcase if
        the invariant can be violated.

        For example, invariant: "balance" must not be 0. We can check if this can be violated and generate a
        testcase::

            m.generate_testcase(state, 'balance CAN be 0', only_if=balance == 0)
            # testcase generated with an input that will violate invariant (make balance == 0)
        """
        try:
            with state as temp_state:
                if only_if is not None:
                    temp_state.constrain(only_if)
                return self._generate_testcase_ex(temp_state, message, name=name)
        except ManticoreError:
            return None

    def _generate_testcase_ex(self, state, message="", name="user"):
        """
        Generate a testcase in the outputspace for the given program state.
        An exception is raised if the state is unsound or unfeasible

        On return you get a Testcase containing all the informations about the state.
        A Testcase is a collection of files living at the OutputSpace.
        Registered plugins and other parts of Manticore add files to the Testcase.
        User can add more streams to is like this:

        testcase = m.generate_testcase_ex(state)
        with testcase.open_stream("txt") as descf:
            descf.write("This testcase is interesting!")

        :param manticore.core.state.State state:
        :param str message: longer description of the testcase condition
        :param str name: short string used as the prefix for the outputspace key (e.g. filename prefix for testcase files)
        :return: a Testcase
        :rtype: bool
        """
        # Refuse to generate a testcase from an unsound state
        if not self.fix_unsound_symbolication(state):
            raise ManticoreError("Trying to generate a testcase out of an unsound state path")

        blockchain = state.platform

        # FIXME. workspace should not be responsible for formating the output
        # each object knows its secrets, and each class should be able to report
        # its final state
        testcase = super().generate_testcase(
            state, message + f"({len(blockchain.human_transactions)} txs)", name=name
        )

        local_findings = set()
        for detector in self.detectors.values():
            for address, pc, finding, at_init, constraint in detector.get_findings(state):
                if (address, pc, finding, at_init) not in local_findings:
                    if state.can_be_true(constraint):
                        local_findings.add((address, pc, finding, at_init, constraint))

        if len(local_findings):
            with testcase.open_stream("findings") as findings:
                for address, pc, finding, at_init, constraint in local_findings:
                    if not state.can_be_true(constraint):
                        continue
                    state.constrain(constraint)
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

            with self.locked_context("ethereum", dict) as ethereum_context:
                functions = ethereum_context.get("symbolic_func", dict())

                for table in functions:
                    concrete_pairs = state.context.get(f"symbolic_func_conc_{table}", ())
                    if concrete_pairs:
                        stream.write(f"Known for {table}:\n")
                        for key, value in concrete_pairs:
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

                logs_summary.write("Address: %x\n" % log_item.address)
                logs_summary.write(
                    "Memlog: %s (%s) %s\n"
                    % (
                        binascii.hexlify(solved_memlog).decode(),
                        printable_bytes(solved_memlog),
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

    @ManticoreBase.at_not_running
    def finalize(self, procs=None, only_alive_states=False):
        """
        Terminate and generate testcases for all currently alive states (contract
        states that cleanly executed to a STOP or RETURN in the last symbolic
        transaction).

        :param procs: force the number of local processes to use in the reporting
        :param bool only_alive_states: if True, killed states (revert/throw/txerror) do not generate testscases
        generation. Uses global configuration constant by default
        """
        if procs is None:
            procs = config.get_group("core").procs

        logger.debug("Finalizing %d states.", self.count_states())

        def finalizer(state_id):
            st = self._load(state_id)
            if self.fix_unsound_symbolication(st):
                last_tx = st.platform.last_transaction
                # Do not generate killed state if only_alive_states is True
                if only_alive_states and last_tx.result in {"REVERT", "THROW", "TXERROR"}:
                    return
                logger.debug("Generating testcase for state_id %d", state_id)
                message = last_tx.result if last_tx else "NO STATE RESULT (?)"
                self.generate_testcase(st, message=message)

        def worker_finalize(q):
            try:
                while True:
                    finalizer(q.get_nowait())
            except EmptyQueue:
                pass

        # Generate testcases for all but killed states
        q = Queue()
        for state_id in self._all_states:
            # we need to remove -1 state before forking because it may be in memory
            q.put(state_id)

        report_workers = [Process(target=worker_finalize, args=(q,)) for _ in range(procs)]
        for proc in report_workers:
            proc.start()

        for proc in report_workers:
            proc.join()

        global_findings = set()
        for state in self.all_states:
            if not self.fix_unsound_symbolication(state):
                continue
            for detector in self.detectors.values():
                for address, pc, finding, at_init, constraint in detector.get_findings(state):
                    if (address, pc, finding, at_init) not in global_findings:
                        if state.can_be_true(constraint):
                            global_findings.add((address, pc, finding, at_init))
        self._global_findings = global_findings

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
            with self.locked_context("ethereum", dict) as ethereum_context:
                functions = ethereum_context.get("symbolic_func", dict())
                for table in functions:
                    concrete_pairs = ethereum_context.get(f"symbolic_func_conc_{table}", ())
                    if concrete_pairs:
                        global_summary.write(f"Known for {table}:\n")
                        for key, value in concrete_pairs:
                            global_summary.write("%s::%x\n" % (binascii.hexlify(key), value))

        for address, md in self.metadata.items():
            with self._output.save_stream("global_%s.sol" % md.name) as global_src:
                global_src.write(md.source_code)

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
        """Returns code coverage for the contract on `account_address`.
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

    @property  # type: ignore
    @ManticoreBase.sync
    @ManticoreBase.at_not_running
    def ready_sound_states(self):
        """
        Iterator over sound ready states.
        This tries to solve any symbolic imprecision added by unsound_symbolication
        and then iterates over the resultant set.

        This is the recommended way to iterate over the resultant states after
        an exploration that included unsound symbolication

        """
        self.fix_unsound_all()
        _ready_states = self._ready_states
        for state_id in _ready_states:
            state = self._load(state_id)
            if self.fix_unsound_symbolication(state):
                yield state
                # Re-save the state in case the user changed its data
                self._save(state, state_id=state_id)

    @property  # type: ignore
    @ManticoreBase.sync
    @ManticoreBase.at_not_running
    def all_sound_states(self):
        """
        Iterator over all sound  states.
        This tries to solve any symbolic imprecision added by unsound_symbolication
        and then iterates over the resultant set.

        This is the recommended to iterate over resultant steas after an exploration
        that included unsound symbolication

        """
        self.fix_unsound_all()
        _ready_states = self._ready_states
        for state_id in _ready_states:
            state = self._load(state_id)
            if self.fix_unsound_symbolication(state):
                yield state
                # Re-save the state in case the user changed its data
                self._save(state, state_id=state_id)

    def fix_unsound_all(self, procs=None):
        """
        :param procs: force the number of local processes to use
        """
        if procs is None:
            procs = config.get_group("core").procs

        # Fix unsoundness in all states
        def finalizer(state_id):
            state = self._load(state_id)
            self.fix_unsound_symbolication(state)
            self._save(state, state_id=state_id)

        def worker_finalize(q):
            try:
                while True:
                    finalizer(q.get_nowait())
            except EmptyQueue:
                pass

        # Generate testcases for all but killed states
        q = Queue()
        for state_id in self._all_states:
            # we need to remove -1 state before forking because it may be in memory
            q.put(state_id)

        report_workers = [Process(target=worker_finalize, args=(q,)) for _ in range(procs)]
        for proc in report_workers:
            proc.start()

        for proc in report_workers:
            proc.join()
