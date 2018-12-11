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
from ..core.smtlib import ConstraintSet, Array, ArrayProxy, BitVec, Operators, BoolConstant, BoolOperation, Expression
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
log.init_logging()


def flagged(flag):
    """
    Return special character denoting concretization happened.
    """
    return '(*)' if flag else ''


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
    method.write(f'{lead_space}Contract: 0x:{address}')
    method.write(f'{lead_space}EVM Program counter: 0x{pc}{" (at constructor)" if at_init else ""}\n')


def calculate_coverage(runtime_bytecode, seen):
    """ Calculates what percentage of runtime_bytecode has been seen """
    count, total = 0, 0
    bytecode = SolidityMetadata._without_metadata(runtime_bytecode)
    for i in EVMAsm.disassemble_all(bytecode):
        if i.pc in seen:
            count += 1
        total += 1

    if total == 0:
        #No runtime_bytecode
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
            name = 'TXBUFFER'
            avoid_collisions = True

        return self.constraints.new_array(index_bits=256, name=name, index_max=size, value_bits=8, taint=frozenset(), avoid_collisions=avoid_collisions)

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
            name = 'TXVALUE'
            avoid_collisions = True
        return self.constraints.new_bitvec(nbits, name=name, avoid_collisions=avoid_collisions)

    def make_symbolic_address(self, name=None, select='both'):
        if select not in ('both', 'normal', 'contract'):
            raise EthereumError('Wrong selection type')
        if select in ('normal', 'contract'):
            # FIXME need to select contracts or normal accounts
            raise NotImplemented
        avoid_collisions = False
        if name is None:
            name = 'TXADDR'
            avoid_collisions = True
        return self.constraints.new_bitvec(160, name=name, avoid_collisions=avoid_collisions)

        constraint = symbolic_address == 0
        for contract_account_i in map(int, self._accounts.values()):
            constraint = Operators.OR(symbolic_address == contract_account_i, constraint)
        self.constrain(constraint)
        return symbolic_address

    def constrain(self, constraint):
        if self.count_states() == 0:
            self.constraints.add(constraint)
        else:
            for state in self.all_states:
                state.constrain(constraint)

    @staticmethod
    def compile(source_code, contract_name=None, libraries=None, runtime=False, solc_bin=None, solc_remaps=[]):
        """ Get initialization bytecode from a Solidity source code """
        name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings = ManticoreEVM._compile(source_code, contract_name, libraries, solc_bin, solc_remaps)
        if runtime:
            return runtime_bytecode
        return init_bytecode

    @staticmethod
    def _link(bytecode, libraries=None):
        has_dependencies = '_' in bytecode
        hex_contract = bytecode
        if has_dependencies:
            deps = {}
            pos = 0
            while pos < len(hex_contract):
                if hex_contract[pos] == '_':
                    # __/tmp/tmp_9k7_l:Manticore______________
                    lib_placeholder = hex_contract[pos:pos + 40]
                    lib_name = lib_placeholder.split(':')[1].split('_')[0]
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
                    hex_contract_lst[pos:pos + 40] = '%040x' % int(lib_address)
            hex_contract = ''.join(hex_contract_lst)
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

        #check solc version
        supported_versions = ('0.4.18', '0.4.21')

        try:
            installed_version_output = check_output([solc, "--version"])
        except OSError:
            raise EthereumError("Solidity compiler not installed.")

        m = re.match(r".*Version: (?P<version>(?P<major>\d+)\.(?P<minor>\d+)\.(?P<build>\d+)).*\+(?P<commit>[^\s]+).*", installed_version_output.decode(), re.DOTALL | re.IGNORECASE)

        if not m or m.groupdict()['version'] not in supported_versions:
            #Fixme https://github.com/trailofbits/manticore/issues/847
            #logger.warning("Unsupported solc version %s", installed_version)
            pass

        # solc path search is a mess
        # https://solidity.readthedocs.io/en/latest/layout-of-source-files.html

        relative_filepath = source_file.name

        if not working_dir:
            working_dir = os.getcwd()
        elif relative_filepath.startswith(working_dir):
            relative_filepath = relative_filepath[len(working_dir) + 1:]

        # If someone pass an absolute path to the file, we don't have to put cwd
        additional_kwargs = {'cwd': working_dir} if working_dir else {}

        solc_invocation = [solc] + list(solc_remaps) + [
            '--combined-json', 'abi,srcmap,srcmap-runtime,bin,hashes,bin-runtime',
            '--allow-paths', '.',
            relative_filepath
        ]

        p = Popen(solc_invocation, stdout=PIPE, stderr=PIPE, **additional_kwargs)
        stdout, stderr = p.communicate()

        stdout, stderr = stdout.decode(), stderr.decode()

        # See #1123 - solc fails when run within snap
        # and https://forum.snapcraft.io/t/interfaces-allow-access-tmp-directory/5129
        if stdout == '' and f'""{relative_filepath}"" is not found' in stderr:
            raise EthereumError(
                'Solidity compilation failed with error: {}\n'
                'Did you install solc from snap Linux universal packages?\n'
                "If so, the problem is likely due to snap's sandbox restricting access to /tmp\n"
                '\n'
                'Here are some potential solutions:\n'
                ' 1) Remove solc from snap and install it different way\n'
                ' 2) Reinstall solc from snap in developer mode, so there is no sandbox\n'
                " 3) Find a way to add /tmp to the solc's sandbox. If you do, "
                "send us a PR so we could add it here!".format(stderr)
            )

        try:
            return json.loads(stdout), stderr
        except ValueError:
            raise EthereumError('Solidity compilation error:\n\n{}'.format(stderr))

    @staticmethod
    def _compile(source_code, contract_name, libraries=None, solc_bin=None, solc_remaps=[], working_dir=None):
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
            with tempfile.NamedTemporaryFile('w+') as temp:
                temp.write(source_code)
                temp.flush()
                output, warnings = ManticoreEVM._run_solc(temp, solc_bin, solc_remaps, working_dir=working_dir)
        elif isinstance(source_code, io.IOBase):
            output, warnings = ManticoreEVM._run_solc(source_code, solc_bin, solc_remaps, working_dir=working_dir)
            source_code.seek(0)
            source_code = source_code.read()
        else:
            raise TypeError(f'source code bad type: {type(source_code).__name__}')

        contracts = output.get('contracts', [])
        if len(contracts) != 1 and contract_name is None:
            raise EthereumError('Solidity file must contain exactly one contract or you must use a contract parameter to specify one.')

        name, contract = None, None
        if contract_name is None:
            name, contract = list(contracts.items())[0]
        else:
            for n, c in contracts.items():
                if n.split(":")[1] == contract_name:
                    name, contract = n, c
                    break

        if name is None:
            raise ValueError('Specified contract not found')

        name = name.split(':')[1]

        if contract['bin'] == '':
            raise EthereumError('Solidity failed to compile your contract.')

        bytecode = ManticoreEVM._link(contract['bin'], libraries)
        srcmap = contract['srcmap'].split(';')
        srcmap_runtime = contract['srcmap-runtime'].split(';')
        hashes = {str(x): str(y) for x, y in contract['hashes'].items()}
        abi = json.loads(contract['abi'])
        runtime = ManticoreEVM._link(contract['bin-runtime'], libraries)
        return name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings

    @property
    def accounts(self):
        return dict(self._accounts)

    def account_name(self, address):
        for name, account in self._accounts.items():
            if account.address == address:
                return name
        return '0x{:x}'.format(address)

    @property
    def normal_accounts(self):
        return {name: account for name, account in self._accounts.items() if not isinstance(account, EVMContract)}

    @property
    def contract_accounts(self):
        return {name: account for name, account in self._accounts.items() if isinstance(account, EVMContract)}

    def get_account(self, name):
        return self._accounts[name]

    def __init__(self, procs=10, workspace_url: str=None, policy: str='random'):
        """
        A Manticore EVM manager
        :param procs:, number of workers to use in the exploration
        :param workspace_url: workspace folder name
        :param policy: scheduling priority
        """
        self._accounts = dict()
        self._serializer = PickleSerializer()

        self._config_procs = procs
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        super().__init__(initial_state, workspace_url=workspace_url, policy=policy)

        self.constraints = ConstraintSet()
        self.detectors = {}
        self.metadata: Dict[int, SolidityMetadata] = {}

        # The following should go to manticore.context so we can use multiprocessing
        self.context['ethereum'] = {}
        self.context['ethereum']['_saved_states'] = set()
        self.context['ethereum']['_final_states'] = set()
        self.context['ethereum']['_completed_transactions'] = 0
        self.context['ethereum']['_sha3_states'] = dict()
        self.context['ethereum']['_known_sha3'] = set()

        self._executor.subscribe('did_load_state', self._load_state_callback)
        self._executor.subscribe('will_terminate_state', self._terminate_state_callback)
        self._executor.subscribe('did_evm_execute_instruction', self._did_evm_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self._did_evm_read_code)
        self._executor.subscribe('on_symbolic_sha3', self._on_symbolic_sha3_callback)
        self._executor.subscribe('on_concrete_sha3', self._on_concrete_sha3_callback)

    @property
    def world(self):
        """ The world instance or None if there is more than one state """
        return self.get_world()

    @property
    def completed_transactions(self):
        with self.locked_context('ethereum') as context:
            return context['_completed_transactions']

    @property
    def _running_state_ids(self):
        """ IDs of the running states"""
        with self.locked_context('ethereum') as context:
            if self.initial_state is not None:
                return (-1,) + tuple(context['_saved_states'])
            else:
                return tuple(context['_saved_states'])

    @property
    def _terminated_state_ids(self):
        """ IDs of the terminated states """
        with self.locked_context('ethereum') as context:
            return tuple(context['_final_states'])

    @property
    def _all_state_ids(self):
        """ IDs of the all states

            Note: state with id -1 is already in memory and it is not backed on the storage
        """
        return self._running_state_ids + self._terminated_state_ids

    @property
    def running_states(self):
        """ Iterates over the running states"""
        for state_id in self._running_state_ids:
            state = self.load(state_id)
            yield state
            self.save(state, state_id=state_id)  # overwrite old

    @property
    def terminated_states(self):
        """ Iterates over the terminated states"""
        for state_id in self._terminated_state_ids:
            state = self.load(state_id)
            yield state
            self.save(state, state_id=state_id)  # overwrite old

    @property
    def all_states(self):
        """ Iterates over the all states (terminated and alive)"""
        for state_id in self._all_state_ids:
            state = self.load(state_id)
            yield state
            self.save(state, state_id=state_id)  # overwrite old

    def count_states(self):
        """ Total states count """
        return len(self._all_state_ids)

    def count_running_states(self):
        """ Running states count """
        return len(self._running_state_ids)

    def count_terminated_states(self):
        """ Terminated states count """
        return len(self._terminated_state_ids)

    def _terminate_state_id(self, state_id):
        """ Manually terminates a states by state_id.
            Moves the state from the running list into the terminated list
        """

        if state_id != -1:
            # Move state from running to final
            with self.locked_context('ethereum') as eth_context:
                saved_states = eth_context['_saved_states']
                final_states = eth_context['_final_states']
                if state_id in saved_states:
                    saved_states.remove(state_id)
                    final_states.add(state_id)
                    eth_context['_saved_states'] = saved_states  # TODO This two may be not needed in py3?
                    eth_context['_final_states'] = final_states
        else:
            assert state_id == -1
            state_id = self.save(self._initial_state, final=True)
            self._initial_state = None
        return state_id

    def _revive_state_id(self, state_id):
        """ Manually revive a state by state_id.
            Moves the state from the final list into the running list
        """

        # Move state from final to running
        if state_id != -1:
            with self.locked_context('ethereum') as eth_context:
                saved_states = eth_context['_saved_states']
                final_states = eth_context['_final_states']
                if state_id in final_states:
                    final_states.remove(state_id)
                    saved_states.add(state_id)
                    eth_context['_saved_states'] = saved_states
                    eth_context['_final_states'] = final_states
        return state_id

    # deprecate this 5 in favor of for sta in m.all_states: do stuff?

    def get_world(self, state_id=None):
        """ Returns the evm world of `state_id` state. """
        state = self.load(state_id)
        if state is None:
            return None
        else:
            return state.platform

    def get_balance(self, address, state_id=None):
        """ Balance for account `address` on state `state_id` """
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_balance(address)

    def get_storage_data(self, address, offset, state_id=None):
        """ Storage data for `offset` on account `address` on state `state_id` """
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_storage_data(address, offset)

    def get_code(self, address, state_id=None):
        """ Storage data for `offset` on account `address` on state `state_id` """
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_code(address)

    def last_return(self, state_id=None):
        """ Last returned buffer for state `state_id` """
        state = self.load(state_id)
        return state.platform.last_return_data

    def transactions(self, state_id=None):
        """ Transactions list for state `state_id` """
        state = self.load(state_id)
        return state.platform.transactions

    def human_transactions(self, state_id=None):
        """ Transactions list for state `state_id` """
        state = self.load(state_id)
        return state.platform.human_transactions

    def make_symbolic_arguments(self, types):
        """
            Make a reasonable serialization of the symbolic argument types
        """
        # FIXME this is more naive than reasonable.
        return ABI.deserialize(types, self.make_symbolic_buffer(32, name='INITARGS', avoid_collisions=True))

    def solidity_create_contract(self, source_code, owner, name=None, contract_name=None, libraries=None,
                                 balance=0, address=None, args=(), solc_bin=None, solc_remaps=[],
                                 working_dir=None, gas=90000):
        """ Creates a solidity contract and library dependencies

            :param str source_code: solidity source code
            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param contract_name: Name of the contract to analyze (optional if there is a single one in the source code)
            :type contract_name: str
            :param balance: balance to be transferred on creation
            :type balance: int or SValue
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
                compile_results = self._compile(source_code, contract_name_i,
                                                libraries=deps, solc_bin=solc_bin, solc_remaps=solc_remaps,
                                                working_dir=working_dir)
                md = SolidityMetadata(*compile_results)
                if contract_name_i == contract_name:
                    constructor_types = md.get_constructor_arguments()

                    if constructor_types != '()':
                        if args is None:
                            args = self.make_symbolic_arguments(constructor_types)

                        constructor_data = ABI.serialize(constructor_types, *args)
                    else:
                        constructor_data = b''

                    contract_account = self.create_contract(owner=owner,
                                                            balance=balance,
                                                            address=address,
                                                            init=md._init_bytecode + constructor_data,
                                                            name=name,
                                                            gas=gas)
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

        if not self.count_running_states() or len(self.get_code(contract_account)) == 0:
            return None
        return contract_account

    def get_nonce(self, address):
        # type forgiveness:
        address = int(address)
        # get all nonces for states containing this address:
        nonces = set(state.platform.get_nonce(address) for state in self.running_states if address in state.platform)
        if not nonces:
            raise NoAliveStates("There are no alive states containing address %x" % address)
        elif len(nonces) != 1:
            # if there are multiple states with this address, they all have to have the same nonce:
            raise EthereumError("Cannot increase the nonce of address %x because it exists in multiple states with different nonces" % address)
        else:
            return next(iter(nonces))

    def create_contract(self, owner, balance=0, address=None, init=None, name=None, gas=21000):
        """ Creates a contract

            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transferred on creation
            :type balance: int or SValue
            :param int address: the address for the new contract (optional)
            :param str init: initializing evm bytecode and arguments
            :param str name: a unique name for reference
            :param gas: gas budget for the creation/initialization of the contract
            :rtype: EVMAccount
        """
        if not self.count_running_states():
            raise NoAliveStates

        nonce = self.get_nonce(owner)
        expected_address = evm.EVMWorld.calculate_new_address(int(owner), nonce=nonce)

        if address is None:
            address = expected_address
        elif address != expected_address:
            raise EthereumError("Address was expected to be %x but was given %x" % (expected_address, address))

        # Name check
        if name is None:
            name = self._get_uniq_name("contract")
        if name in self._accounts:
            # Account name already used
            raise EthereumError("Name already used")

        self._transaction('CREATE', owner, balance, address, data=init, gaslimit=gas)
        # TODO detect failure in the constructor

        self._accounts[name] = EVMContract(address=address, manticore=self, default_caller=owner, name=name)
        return self.accounts[name]

    def _get_uniq_name(self, stem):
        count = 0
        for name_i in self.accounts.keys():
            if name_i.startswith(stem):
                try:
                    count = max(count, int(name_i[len(stem):]) + 1)
                except:
                    pass
        name = "{:s}{:d}".format(stem, count)
        assert name not in self.accounts
        return name

    def _all_addresses(self):
        """ Returns all addresses in all running states """
        ret = set()
        for state in self.running_states:
            ret |= set(state.platform.accounts)
        return ret

    def new_address(self):
        """ Create a fresh 160bit address """
        all_addresses = self._all_addresses()
        while True:
            new_address = random.randint(100, pow(2, 160))
            if new_address not in all_addresses:
                return new_address

    def transaction(self, caller, address, value, data, gas=21000):
        """ Issue a symbolic transaction in all running states

            :param caller: the address of the account sending the transaction
            :type caller: int or EVMAccount
            :param address: the address of the contract to call
            :type address: int or EVMAccount
            :param value: balance to be transfered on creation
            :type value: int or SValue
            :param data: initial data
            :param gas: gas budget
            :raises NoAliveStates: if there are no alive states to execute
        """
        self._transaction('CALL', caller, value=value, address=address, data=data, gaslimit=gas)

    def create_account(self, balance=0, address=None, code=None, name=None):
        """ Low level creates an account. This won't generate a transaction.

            :param balance: balance to be set on creation (optional)
            :type balance: int or SValue
            :param address: the address for the new account (optional)
            :type address: int
            :param code: the runtime code for the new account (None means normal account) (optional)
            :param name: a global account name eg. for use as reference in the reports (optional)
            :return: an EVMAccount
        """
        # Need at least one state where to apply this
        if not self.count_running_states():
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

        #Balance check
        if not isinstance(balance, int):
            raise EthereumError("Balance invalid type")

        if isinstance(code, str):
            code = bytearray(code)
        if code is not None and not isinstance(code, (bytearray, Array)):
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
        for state in self.running_states:
            world = state.platform

            if '_pending_transaction' in state.context:
                raise EthereumError("This is bad. There should not be a pending transaction")

            if address in world.accounts:
                # Address already used
                raise EthereumError("This is bad. Same address is used for different contracts in different states")
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

    def _transaction(self, sort, caller, value=0, address=None, data=None, gaslimit=0, price=1):
        """ Initiates a transaction

            :param caller: caller account
            :type caller: int or EVMAccount
            :param int address: the address for the transaction (optional)
            :param value: value to be transferred
            :param price: the price of gas for this transaction. Mostly unused.
            :type value: int or SValue
            :param str data: initializing evm bytecode and arguments or transaction call data
            :param gaslimit: gas budget
            :rtype: EVMAccount
        """
        #Type Forgiveness
        if isinstance(address, EVMAccount):
            address = int(address)
        if isinstance(caller, EVMAccount):
            caller = int(caller)
        #Defaults, call data is empty
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
        if sort not in ('CREATE', 'CALL'):
            raise ValueError('unsupported transaction type')

        if sort == 'CREATE':
            # When creating data is the init_bytecode + arguments
            if len(data) == 0:
                raise EthereumError("An initialization bytecode is needed for a CREATE")

        assert address is not None
        assert caller is not None

        # Transactions (like everything else) need at least one running state
        if not self.count_running_states():
            raise NoAliveStates

        # To avoid going full crazy, we maintain a global list of addresses
        for state in self.running_states:
            world = state.platform

            if '_pending_transaction' in state.context:
                raise EthereumError("This is bad. It should not be a pending transaction")

            # Choose an address here, because it will be dependent on the caller's nonce in this state
            if address is None:
                if issymbolic(caller):
                    # TODO (ESultanik): In order to handle this case, we are going to have to do something like fork
                    # over all possible caller addresses.
                    # But this edge case will likely be extremely rare, if ever ecountered.
                    raise EthereumError("Manticore does not currently support contracts with symbolic addresses creating new contracts")
                address = world.new_address(caller)

            # Migrate any expression to state specific constraint set
            caller_migrated, address_migrated, value_migrated, data_migrated = self._migrate_tx_expressions(state, caller, address, value, data)

            # Different states may CREATE a different set of accounts. Accounts
            # that were crated by a human have the same address in all states.
            # This diverges from the yellow paper but at least we check that we
            # are not trying to create an already used address here
            if sort == 'CREATE':
                if address in world.accounts:
                    # Address already used
                    raise EthereumError("This is bad. Same address is used for different contracts in different states")

            state.context['_pending_transaction'] = (sort, caller_migrated, address_migrated, value_migrated, data_migrated, gaslimit, price)

        # run over potentially several states and
        # generating potentially several others
        self.run(procs=self._config_procs)

        return address

    def preconstraint_for_call_transaction(self, address: Union[int, EVMAccount], data: Array,
                                           value: Optional[Union[int, Expression]] = None,
                                           contract_metadata: Optional[SolidityMetadata] = None) -> BoolOperation:
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
            if value_is_symbolic and not contract_metadata.get_abi(selector)['payable']:
                c = Operators.AND(c, value == 0)
            if constraint is None:
                constraint = c
            else:
                constraint = Operators.OR(constraint, c)

        return constraint

    def multi_tx_analysis(self, solidity_filename, working_dir=None, contract_name=None,
                          tx_limit=None, tx_use_coverage=True,
                          tx_send_ether=True, tx_account="attacker", tx_preconstrain=False, args=None):
        owner_account = self.create_account(balance=1000, name='owner')
        attacker_account = self.create_account(balance=1000, name='attacker')

        # Pretty print
        logger.info("Starting symbolic create contract")

        with open(solidity_filename) as f:
            contract_account = self.solidity_create_contract(f, contract_name=contract_name, owner=owner_account,
                                                             args=args, working_dir=working_dir)

        if tx_account == "attacker":
            tx_account = [attacker_account]
        elif tx_account == "owner":
            tx_account = [owner_account]
        elif tx_account == "combo1":
            tx_account = [owner_account, attacker_account]
        else:
            raise EthereumError('The account to perform the symbolic exploration of the contract should be "attacker", "owner" or "combo1"')

        if contract_account is None:
            logger.info("Failed to create contract: exception in constructor")
            return

        prev_coverage = 0
        current_coverage = 0
        tx_no = 0
        while (current_coverage < 100 or not tx_use_coverage) and not self.is_shutdown():
            try:
                logger.info("Starting symbolic transaction: %d", tx_no)

                # run_symbolic_tx
                symbolic_data = self.make_symbolic_buffer(320)
                if tx_send_ether:
                    value = self.make_symbolic_value()
                else:
                    value = 0

                if tx_preconstrain:
                    self.constrain(self.preconstraint_for_call_transaction(address=contract_account,
                                                                           data=symbolic_data,
                                                                           value=value))

                self.transaction(caller=tx_account[min(tx_no, len(tx_account) - 1)],
                                 address=contract_account,
                                 data=symbolic_data,
                                 value=value,
                                 gas=2100000)
                logger.info("%d alive states, %d terminated states", self.count_running_states(), self.count_terminated_states())
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
        """ Run any pending transaction on any running state """
        # Check if there is a pending transaction
        with self.locked_context('ethereum') as context:
            # there are no states added to the executor queue
            assert len(self._executor.list()) == 0
            for state_id in context['_saved_states']:
                self._executor.put(state_id)
            context['_saved_states'] = set()

        # A callback will use _pending_transaction and issue the transaction
        # in each state (see load_state_callback)
        super().run(**kwargs)

        with self.locked_context('ethereum') as context:
            if len(context['_saved_states']) == 1:
                self._initial_state = self._executor._workspace.load_state(context['_saved_states'].pop(), delete=True)
                self._executor.forward_events_from(self._initial_state, True)
                context['_saved_states'] = set()
                assert self._running_state_ids == (-1,)

    def save(self, state, state_id=None, final=False):
        """ Save a state in secondary storage and add it to running or final lists

            :param state: A manticore State
            :param state_id: if not None force state_id (overwrite)
            :param final: True if state is final
            :returns: a state id
        """
        # If overwriting then the state_id must be known
        if state_id is not None:
            if state_id not in self._all_state_ids:
                raise EthereumError("Trying to overwrite unknown state_id")
            with self.locked_context('ethereum') as context:
                context['_final_states'].discard(state_id)
                context['_saved_states'].discard(state_id)

        if state_id != -1:
            # save the state to secondary storage
            state_id = self._executor._workspace.save_state(state, state_id=state_id)

            with self.locked_context('ethereum') as context:
                if final:
                    # Keep it on a private list
                    context['_final_states'].add(state_id)
                else:
                    # Keep it on a private list
                    context['_saved_states'].add(state_id)
        return state_id

    def load(self, state_id=None):
        """ Load one of the running or final states.

            :param state_id: If None it assumes there is a single running state
            :type state_id: int or None
        """
        state = None
        if state_id is None:
            #a single state was assumed
            state_count = self.count_running_states()
            if state_count == 1:
                #Get the ID of the single running state
                state_id = self._running_state_ids[0]
            elif state_count == 0:
                raise NoAliveStates
            else:
                raise EthereumError("More than one state running; you must specify a state id.")

        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)
            #froward events from newly loaded object
            self._executor.forward_events_from(state, True)
        return state

    # Callbacks
    def _on_symbolic_sha3_callback(self, state, data, known_hashes):
        """ INTERNAL USE """
        assert issymbolic(data), 'Data should be symbolic here!'

        with self.locked_context('ethereum') as context:
            known_sha3 = context.get('_known_sha3', None)
            if known_sha3 is None:
                known_sha3 = set()

            sha3_states = context.get('_sha3_states', [])
            results = []
            # If know_hashes is true then there is a _known_ solution for the hash
            known_hashes_cond = False
            for key, value in known_sha3:
                assert not issymbolic(key), "Saved sha3 data,hash pairs should be concrete"
                cond = key == data

                #TODO consider disabling this solver query.
                if not state.can_be_true(cond):
                    continue

                results.append((key, value))
                known_hashes_cond = Operators.OR(cond, known_hashes_cond)

            # adding a single random example so we can explore further in case
            # there are not known sha3 pairs that match yet
            if not results:
                data_concrete = state.solve_one(data)
                s = sha3.keccak_256(data_concrete)
                data_hash = int(s.hexdigest(), 16)
                results.append((data_concrete, data_hash))
                known_hashes_cond = data_concrete == data
                known_sha3.add((data_concrete, data_hash))
            not_known_hashes_cond = Operators.NOT(known_hashes_cond)

            # We need to fork/save the state
            #################################
            # save the state to secondary storage
            # Build and enqueue a state for each solution
            with state as temp_state:
                if temp_state.can_be_true(not_known_hashes_cond):
                    temp_state.constrain(not_known_hashes_cond)
                    state_id = self._executor._workspace.save_state(temp_state)
                    sha3_states[state_id] = [hsh for buf, hsh in known_sha3]
            context['_sha3_states'] = sha3_states

            if not state.can_be_true(known_hashes_cond):
                raise TerminateState("There is no matching sha3 pair, bailing out")
            state.constrain(known_hashes_cond)

            #send known hashes to evm
            known_hashes.update(results)

    def _on_concrete_sha3_callback(self, state, buf, value):
        """ INTERNAL USE """
        with self.locked_context('ethereum', dict) as ethereum_context:
            known_sha3 = ethereum_context.get('_known_sha3', None)
            if known_sha3 is None:
                known_sha3 = set()
            known_sha3.add((buf, value))
            ethereum_context['_known_sha3'] = known_sha3

    def _terminate_state_callback(self, state, state_id, e):
        """ INTERNAL USE
            Every time a state finishes executing the last transaction, we save it in
            our private list
        """
        if isinstance(e, AbandonState):
            #do nothing
            return
        world = state.platform
        state.context['last_exception'] = e
        e.testcase = False  # Do not generate a testcase file

        if not world.all_transactions:
            logger.debug("Something went wrong: search terminated in the middle of an ongoing tx")
            self.save(state, final=True)
            return

        tx = world.all_transactions[-1]

        #we initiated the Tx; we need process the outcome for now.
        #Fixme incomplete.
        if tx.is_human():
            if tx.sort == 'CREATE':
                if tx.result == 'RETURN':
                    world.set_code(tx.address, tx.return_data)
                else:
                    world.delete_account(tx.address)
        else:
            logger.info("Manticore exception: state should be terminated only at the end of the human transaction")

        #Human tx that ends in this wont modify the storage so finalize and
        # generate a testcase. FIXME This should be configurable as REVERT and
        # THROW; it actually changes the balance and nonce? of some accounts
        if tx.result in {'SELFDESTRUCT', 'REVERT', 'THROW', 'TXERROR'}:
            self.save(state, final=True)
        elif tx.result in {'RETURN', 'STOP'}:
            # if not a revert, we save the state for further transactions
            self.save(state)  # Add to running states
        else:
            logger.debug("Exception in state. Discarding it")

    #Callbacks
    def _load_state_callback(self, state, state_id):
        """ INTERNAL USE
            If a state was just loaded from storage, we do the pending transaction
        """
        if '_pending_transaction' not in state.context:
            return
        world = state.platform
        ty, caller, address, value, data, gaslimit, price = state.context['_pending_transaction']
        del state.context['_pending_transaction']

        if ty == 'CALL':
            world.transaction(address=address, caller=caller, data=data, value=value, price=price, gas=gaslimit)
        else:
            assert ty == 'CREATE'
            world.create_contract(caller=caller, address=address, balance=value, init=data, price=price, gas=gaslimit)

    def _did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
        """ INTERNAL USE """
        #logger.debug("%s", state.platform.current_vm)
        #TODO move to a plugin
        at_init = state.platform.current_transaction.sort == 'CREATE'
        if at_init:
            coverage_context_name = 'init_coverage'
        else:
            coverage_context_name = 'runtime_coverage'

        with self.locked_context(coverage_context_name, set) as coverage:
            coverage.add((state.platform.current_vm.address, instruction.pc))

        state.context.setdefault('evm.trace', []).append((state.platform.current_vm.address, instruction.pc, at_init))

    def _did_evm_read_code(self, state, offset, size):
        """ INTERNAL USE """
        with self.locked_context('code_data', set) as code_data:
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
        return self._executor._workspace._store.uri

    def generate_testcase(self, state, message='', only_if=None, name='user'):
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
        if only_if is None:
            self._generate_testcase_callback(state, name, message)
            return True
        else:
            with state as temp_state:
                temp_state.constrain(only_if)
                if temp_state.is_feasible():
                    self._generate_testcase_callback(temp_state, name, message)
                    return True

        return False

    def current_location(self, state):
        world = state.platform
        address = world.current_vm.address
        pc = world.current_vm.pc
        at_init = world.current_transaction.sort == 'CREATE'
        output = io.StringIO()
        write_findings(output, '', address, pc, at_init)
        md = self.get_metadata(address)
        if md is not None:
            src = md.get_source_for(pc, runtime=not at_init)
            output.write('Snippet:\n')
            output.write(src.replace('\n', '\n  ').strip())
            output.write('\n')
        return output.getvalue()

    def _generate_testcase_callback(self, state, name, message=''):
        """
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        """
        # workspace should not be responsible for formating the output
        # each object knows its secrets, and each class should be able to report its
        # final state
        #super()._generate_testcase_callback(state, name, message)
        # TODO(mark): Refactor ManticoreOutput to let the platform be more in control
        #  so this function can be fully ported to EVMWorld.generate_workspace_files.
        blockchain = state.platform

        testcase = self._output.testcase(name.replace(' ', '_'))
        last_tx = blockchain.last_transaction
        if last_tx:
            message = message + last_tx.result
        logger.info("Generated testcase No. {} - {}".format(testcase.num, message))

        local_findings = set()
        for detector in self.detectors.values():
            for address, pc, finding, at_init, constraint in detector.get_findings(state):
                if (address, pc, finding, at_init) not in local_findings:
                    local_findings.add((address, pc, finding, at_init, constraint))

        if len(local_findings):
            with testcase.open_stream('findings') as findings:
                for address, pc, finding, at_init, constraint in local_findings:
                    findings.write('- %s -\n' % finding)
                    write_findings(findings, '  ', address, pc, at_init)
                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc, runtime=not at_init)
                        findings.write('  Snippet:\n')
                        findings.write(src.replace('\n', '\n    ').strip())
                        findings.write('\n')

        with testcase.open_stream('summary') as stream:
            is_something_symbolic = state.platform.dump(stream, state, self, message)

            with self.locked_context('ethereum') as context:
                known_sha3 = context.get('_known_sha3', None)
                if known_sha3:
                    stream.write("Known hashes:\n")
                    for key, value in known_sha3:
                        stream.write('%s::%x\n' % (binascii.hexlify(key), value))

            if is_something_symbolic:
                stream.write('\n\n(*) Example solution given. Value is symbolic and may take other values\n')

        # Transactions

        with testcase.open_stream('tx') as tx_summary:
            with testcase.open_stream('tx.json') as txjson:
                txlist = []
                is_something_symbolic = False

                for sym_tx in blockchain.human_transactions:  # external transactions
                    tx_summary.write("Transactions No. %d\n" % blockchain.transactions.index(sym_tx))

                    conc_tx = sym_tx.concretize(state)
                    txlist.append(conc_tx.to_dict(self))

                    is_something_symbolic = sym_tx.dump(tx_summary, state, self, conc_tx=conc_tx)

                if is_something_symbolic:
                    tx_summary.write('\n\n(*) Example solution given. Value is symbolic and may take other values\n')

                json.dump(txlist, txjson)

        # logs
        with testcase.open_stream('logs') as logs_summary:
            is_something_symbolic = False
            for log_item in blockchain.logs:
                is_log_symbolic = issymbolic(log_item.memlog)
                is_something_symbolic = is_log_symbolic or is_something_symbolic
                solved_memlog = state.solve_one(log_item.memlog)
                printable_bytes = ''.join([c for c in map(chr, solved_memlog) if c in string.printable])

                logs_summary.write("Address: %x\n" % log_item.address)
                logs_summary.write("Memlog: %s (%s) %s\n" % (binascii.hexlify(solved_memlog).decode(), printable_bytes, flagged(is_log_symbolic)))
                logs_summary.write("Topics:\n")
                for i, topic in enumerate(log_item.topics):
                    logs_summary.write("\t%d) %x %s" % (i, state.solve_one(topic), flagged(issymbolic(topic))))

        with testcase.open_stream('constraints') as smt_summary:
            smt_summary.write(str(state.constraints))

        with testcase.open_stream('pkl', binary=True) as statef:
            self._serializer.serialize(state, statef)

        trace = state.context.get('evm.trace')
        if trace:
            with testcase.open_stream('trace') as f:
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
                filestream.write('---\n')
            ln = '0x{:x}:0x{:x} {}\n'.format(contract, pc, '*' if at_init else '')
            filestream.write(ln)

    @property
    def global_findings(self):
        global_findings = set()
        for detector in self.detectors.values():
            for address, pc, finding, at_init in detector.global_findings:
                if (address, pc, finding, at_init) not in global_findings:
                    global_findings.add((address, pc, finding, at_init))
        return global_findings

    def finalize(self):
        """
        Terminate and generate testcases for all currently alive states (contract states that cleanly executed
        to a STOP or RETURN in the last symbolic transaction).
        """
        logger.debug("Finalizing %d states.", self.count_states())

        def finalizer(state_id):
            state_id = self._terminate_state_id(state_id)
            st = self.load(state_id)
            logger.debug("Generating testcase for state_id %d", state_id)
            self._generate_testcase_callback(st, 'test', '')

        def worker_finalize(q):
            try:
                while True:
                    finalizer(q.get_nowait())
            except EmptyQueue:
                pass

        q = Queue()
        for state_id in self._all_state_ids:
            #we need to remove -1 state before forking because it may be in memory
            if state_id == -1:
                finalizer(-1)
            else:
                q.put(state_id)

        report_workers = []
        for _ in range(self._config_procs):
            proc = Process(target=worker_finalize, args=(q,))
            proc.start()
            report_workers.append(proc)

        for proc in report_workers:
            proc.join()

        # global summary
        if len(self.global_findings):
            with self._output.save_stream('global.findings') as global_findings:
                for address, pc, finding, at_init in self.global_findings:
                    global_findings.write('- %s -\n' % finding)
                    write_findings(global_findings, '  ', address, pc, at_init)
                    md = self.get_metadata(address)
                    if md is not None:
                        source_code_snippet = md.get_source_for(pc, runtime=not at_init)
                        global_findings.write('  Solidity snippet:\n')
                        global_findings.write('    '.join(source_code_snippet.splitlines(True)))
                        global_findings.write('\n')

        self._save_run_data()

        with self._output.save_stream('global.summary') as global_summary:
            # (accounts created by contract code are not in this list )
            global_summary.write("Global runtime coverage:\n")
            for address in self.contract_accounts.values():
                global_summary.write("{:x}: {:2.2f}%\n".format(int(address), self.global_coverage(address)))

                md = self.get_metadata(address)
                if md is not None and len(md.warnings) > 0:
                    global_summary.write('\n\nCompiler warnings for %s:\n' % md.name)
                    global_summary.write(md.warnings)

        for address, md in self.metadata.items():
            with self._output.save_stream('global_%s.sol' % md.name) as global_src:
                global_src.write(md.source_code)
            with self._output.save_stream('global_%s_runtime.bytecode' % md.name, binary=True) as global_runtime_bytecode:
                global_runtime_bytecode.write(md.runtime_bytecode)
            with self._output.save_stream('global_%s_init.bytecode' % md.name, binary=True) as global_init_bytecode:
                global_init_bytecode.write(md.init_bytecode)

            with self._output.save_stream('global_%s.runtime_asm' % md.name) as global_runtime_asm:
                runtime_bytecode = md.runtime_bytecode

                with self.locked_context('runtime_coverage') as seen:

                    count, total = 0, 0
                    for i in EVMAsm.disassemble_all(runtime_bytecode):
                        if (address, i.pc) in seen:
                            count += 1
                            global_runtime_asm.write('*')
                        else:
                            global_runtime_asm.write(' ')

                        global_runtime_asm.write('%4x: %s\n' % (i.pc, i))
                        total += 1

            with self._output.save_stream('global_%s.init_asm' % md.name) as global_init_asm:
                with self.locked_context('init_coverage') as seen:
                    count, total = 0, 0
                    for i in EVMAsm.disassemble_all(md.init_bytecode):
                        if (address, i.pc) in seen:
                            count += 1
                            global_init_asm.write('*')
                        else:
                            global_init_asm.write(' ')

                        global_init_asm.write('%4x: %s\n' % (i.pc, i))
                        total += 1

            with self._output.save_stream('global_%s.init_visited' % md.name) as f:
                with self.locked_context('init_coverage') as seen:
                    visited = set((o for (a, o) in seen if a == address))
                    for o in sorted(visited):
                        f.write('0x%x\n' % o)

            with self._output.save_stream('global_%s.runtime_visited' % md.name) as f:
                with self.locked_context('runtime_coverage') as seen:
                    visited = set()
                    for (a, o) in seen:
                        if a == address:
                            visited.add(o)
                    for o in sorted(visited):
                        f.write('0x%x\n' % o)

        # delete actual streams from storage
        for state_id in self._all_state_ids:
            # state_id -1 is always only on memory
            if state_id != -1:
                self._executor._workspace.rm_state(state_id)

        # clean up lists
        with self.locked_context('ethereum') as eth_context:
            eth_context['_saved_states'] = set()
            eth_context['_final_states'] = set()

    def global_coverage(self, account):
        """ Returns code coverage for the contract on `account_address`.
            This sums up all the visited code lines from any of the explored
            states.
        """
        account_address = int(account)
        runtime_bytecode = None
        #Search one state in which the account_address exists
        for state in self.all_states:
            world = state.platform
            if account_address in world:
                code = world.get_code(account_address)
                runtime_bytecode = state.solve_one(code)
                break
        else:
            return 0.0
        with self.locked_context('runtime_coverage') as coverage:
            seen = {off for addr, off in coverage if addr == account_address}
        return calculate_coverage(runtime_bytecode, seen)

    # TODO: Find a better way to suppress execution of Manticore._did_finish_run_callback
    # We suppress because otherwise we log it many times and it looks weird.
    def _did_finish_run_callback(self):
        pass

    def __repr__(self):
        return self.__str__()

    def __str__(self):
        return "<ManticoreEVM | Alive States: {}; Terminated States: {}>".format(
            self.count_running_states(),
            self.count_terminated_states()
        )
