from typing import Optional

from . import abitypes
import uuid
import numbers
import random
import hashlib
import binascii
import string
import re
import os
import pyevmasm as EVMAsm
from . import Manticore
from .manticore import ManticoreError
from .core.smtlib import ConstraintSet, Operators, solver, issymbolic, istainted, taint_with, get_taints, BitVec, Constant, operators, Array, ArrayVariable, ArrayProxy
from .platforms import evm
from .core.state import State
from .utils.helpers import istainted, issymbolic, PickleSerializer
import tempfile
from subprocess import Popen, PIPE, check_output
from multiprocessing import Process, Queue
from queue import Empty as EmptyQueue
import sha3
import json
import logging
import io
from .core.plugin import Plugin
from functools import reduce
from contextlib import contextmanager
logger = logging.getLogger(__name__)


class EthereumError(ManticoreError):
    pass


class DependencyError(EthereumError):
    def __init__(self, lib_names):
        super().__init__("You must pre-load and provide libraries addresses{ libname:address, ...} for %r" % lib_names)
        self.lib_names = lib_names


class NoAliveStates(EthereumError):
    pass


#
# Plugins
#


class FilterFunctions(Plugin):
    def __init__(self, regexp=r'.*', mutability='both', depth='both', fallback=False, include=True, **kwargs):
        """
            Constrain input based on function metadata. Include or avoid functions selected by the specified criteria.

            Examples:
            #Do not explore any human transactions that end up calling a constant function
            no_human_constant = FilterFunctions(depth='human', mutability='constant', include=False)

            #At human tx depth only accept synthetic check functions
            only_tests = FilterFunctions(regexp=r'mcore_.*', depth='human', include=False)

            :param regexp: a regular expresion over the name of the function '.*' will match all functions
            :param mutability: mutable, constant or both will match functions declared in the abi to be of such class
            :param depth: match functions in internal transactions, in human initiated transactions or in both types
            :param fallback: if True include the fallback function. Hash will be 00000000 for it
            :param include: if False exclude the selected functions, if True include them
        """
        super().__init__(**kwargs)
        depth = depth.lower()
        if depth not in ('human', 'internal', 'both'):
            raise ValueError
        mutability = mutability.lower()
        if mutability not in ('mutable', 'constant', 'both'):
            raise ValueError

        #fixme better names for member variables
        self._regexp = regexp
        self._mutability = mutability
        self._depth = depth
        self._fallback = fallback
        self._include = include

    def will_open_transaction_callback(self, state, tx):
        world = state.platform
        tx_cnt = len(world.all_transactions)
        # Constrain input only once per tx, per plugin
        if state.context.get('constrained%d' % id(self), 0) != tx_cnt:
            state.context['constrained%d' % id(self)] = tx_cnt

            if self._depth == 'human' and not tx.is_human:
                return
            if self._depth == 'internal' and tx.is_human:
                return

            #Get metadata if any for the targe addreess of current tx
            md = self.manticore.get_metadata(tx.address)
            if md is None:
                return
            #Lets compile  the list of interesting hashes
            selected_functions = []

            for func_hsh in md.hashes:
                if func_hsh == '00000000':
                    continue
                abi = md.get_abi(func_hsh)
                func_name = md.get_func_name(func_hsh)
                if self._mutability == 'constant' and not abi.get('constant', False):
                    continue
                if self._mutability == 'mutable' and abi.get('constant', False):
                    continue
                if not re.match(self._regexp, func_name):
                    continue
                selected_functions.append(func_hsh)

            if self._fallback:
                selected_functions.append('00000000')

            if self._include:
                # constraint the input so it can take only the interesting values
                constraint = reduce(Operators.OR, (tx.data[:4] == x for x in selected_functions))
                state.constrain(constraint)
            else:
                #Avoid all not selected hashes
                for func_hsh in md.hashes:
                    if func_hsh in selected_functions:
                        constraint = tx.data[:4] != func_hsh
                        state.constrain(constraint)


class LoopDepthLimiter(Plugin):
    ''' This just abort explorations too deep '''

    def __init__(self, loop_count_threshold=5, **kwargs):
        super().__init__(**kwargs)
        self.loop_count_threshold = loop_count_threshold

    def will_start_run_callback(self, *args):
        with self.manticore.locked_context('seen_rep', dict) as reps:
            reps.clear()

    def will_execute_instruction_callback(self, state, pc, insn):
        world = state.platform
        with self.manticore.locked_context('seen_rep', dict) as reps:
            item = (world.current_transaction.sort == 'CREATE', world.current_transaction.address, pc)
            if item not in reps:
                reps[item] = 0
            reps[item] += 1
            if reps[item] > self.loop_count_threshold:
                state.abandon()


#
# Detectors
#


class Detector(Plugin):
    @property
    def name(self):
        return self.__class__.__name__.split('.')[-1]

    def get_findings(self, state):
        return state.context.setdefault('{:s}.findings'.format(self.name), set())

    @contextmanager
    def locked_global_findings(self):
        with self.manticore.locked_context('{:s}.global_findings'.format(self.name), set) as global_findings:
            yield global_findings

    @property
    def global_findings(self):
        with self.locked_global_findings() as global_findings:
            return global_findings

    def add_finding(self, state, address, pc, finding, at_init, constraint=True):
        '''
        Logs a finding at specified contract and assembler line.
        :param state: current state
        :param address: contract address of the finding
        :param pc: program counter of the finding
        :param at_init: true if executing the constructor
        :param finding: textual description of the finding
        :param constraint: finding is considered reproducible only when constraint is True
        '''

        if isinstance(pc, Constant):
            pc = pc.value
        if not isinstance(pc, int):
            raise ValueError("PC must be a number")
        self.get_findings(state).add((address, pc, finding, at_init, constraint))
        with self.locked_global_findings() as gf:
            gf.add((address, pc, finding, at_init))
        #Fixme for ever broken logger
        logger.warning(finding)

    def add_finding_here(self, state, finding, constraint=True):
        '''
        Logs a finding in current contract and assembler line.
        :param state: current state
        :param finding: textual description of the finding
        :param constraint: finding is considered reproducible only when constraint is True
        '''
        address = state.platform.current_vm.address
        pc = state.platform.current_vm.pc
        if isinstance(pc, Constant):
            pc = pc.value
        if not isinstance(pc, int):
            raise ValueError("PC must be a number")
        at_init = state.platform.current_transaction.sort == 'CREATE'
        self.add_finding(state, address, pc, finding, at_init, constraint)

    def _save_current_location(self, state, finding, condition=True):
        '''
        Save current location in the internal locations list and returns a textual id for it.
        This is used to save locations that could later be promoted to a finding if other conditions hold
        See _get_location()
        :param state: current state
        :param finding: textual description of the finding
        :param condition: general purpose constraint
        '''
        address = state.platform.current_vm.address
        pc = state.platform.current_vm.pc
        at_init = state.platform.current_transaction.sort == 'CREATE'
        location = (address, pc, finding, at_init, condition)
        hash_id = hashlib.sha1(str(location).encode()).hexdigest()
        state.context.setdefault('{:s}.locations'.format(self.name), {})[hash_id] = location
        return hash_id

    def _get_location(self, state, hash_id):
        ''' Get previously saved location
            A location is composed of: address, pc, finding, at_init, condition
        '''
        return state.context.setdefault('{:s}.locations'.format(self.name), {})[hash_id]

    def _get_src(self, address, pc):
        return self.manticore.get_metadata(address).get_source_for(pc)


class VerboseTrace(Plugin):
    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        current_vm = state.platform.current_vm
        state.setdefault('str_trace', []).append(str(current_vm))

    def on_finalize(self, state, testcase):
        with testcase.open_stream('str_trace') as str_trace_f:
            str_trace_f.write('\n'.join(state.context.get('str_trace', [])))


class DetectEnvInstruction(Detector):
    ''' Detect the usage of instructions that query environmental/block information:
        BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT, ORIGIN, GASPRICE

        Sometimes environmental information can be manipulated. Contracts should avoid
        using it. Unless special situations. Notably to programatically detect human transactions
        `sender == origin`
    '''

    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        if instruction.semantics in ('BLOCKHASH', 'COINBASE', 'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'GASLIMIT', 'ORIGIN', 'GASPRICE'):
            self.add_finding_here(state, f'Warning {instruction.semantics} instruction used')


class DetectSelfdestruct(Detector):
    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        if instruction.semantics == 'SELFDESTRUCT':
            self.add_finding_here(state, 'Reachable SELFDESTRUCT')


class DetectExternalCallAndLeak(Detector):
    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        if instruction.semantics == 'CALL':
            dest_address = arguments[1]
            sent_value = arguments[2]
            msg_sender = state.platform.current_vm.caller

            msg = 'ether leak' if state.can_be_true(sent_value != 0) else 'external call'

            if issymbolic(dest_address):
                # We assume dest_address is symbolic because it came from symbolic tx data (user input argument)
                if state.can_be_true(msg_sender == dest_address):
                    self.add_finding_here(state, f"Reachable {msg} to sender via argument", constraint=msg_sender == dest_address)
                else:
                    # This might be a false positive if the dest_address can't actually be solved to anything
                    # useful/exploitable
                    self.add_finding_here(state, f"Reachable {msg} to user controlled address via argument", constraint=msg_sender != dest_address)
            else:
                if msg_sender == dest_address:
                    self.add_finding_here(state, f"Reachable {msg} to sender")


class DetectInvalid(Detector):
    def __init__(self, only_human=True, **kwargs):
        """
        Detects INVALID instructions.

        INVALID instructions are originally designated to signal exceptional code.
        As in practice the INVALID instruction is used in different ways this
        detector may Generate a great deal of false positives.

        :param only_human: if True report only INVALID at depth 0 transactions
        """
        super().__init__(**kwargs)
        self._only_human = only_human

    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        mnemonic = instruction.semantics

        if mnemonic == 'INVALID':
            if not self._only_human or state.platform.current_transaction.depth == 0:
                self.add_finding_here(state, "INVALID instruction")


class DetectReentrancySimple(Detector):
    """
    Simple detector for reentrancy bugs.
    Alert if contract changes the state of storage (does a write) after a call with >2300 gas to a user controlled/symbolic
    external address or the msg.sender address.
    """

    @property
    def _context_key(self):
        return f'{self.name}.call_locations'

    def will_open_transaction_callback(self, state, tx):
        if tx.is_human():
            state.context[self._context_key] = []

    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        if instruction.semantics == 'CALL':
            gas = arguments[0]
            dest_address = arguments[1]
            msg_sender = state.platform.current_vm.caller
            pc = state.platform.current_vm.pc

            is_enough_gas = Operators.UGT(gas, 2300)
            if not state.can_be_true(is_enough_gas):
                return

            # flag any external call that's going to a symbolic/user controlled address, or that's going
            # concretely to the sender's address
            if issymbolic(dest_address) or msg_sender == dest_address:
                state.context.get(self._context_key, []).append((pc, is_enough_gas))

    def did_evm_write_storage_callback(self, state, address, offset, value):
        locs = state.context.get(self._context_key, [])

        # if we're here and locs has stuff in it. by definition this state has
        # encountered a dangerous call and is now at a write.
        for callpc, gas_constraint in locs:
            addr = state.platform.current_vm.address
            at_init = state.platform.current_transaction.sort == 'CREATE'
            self.add_finding(state, addr, callpc, 'Potential reentrancy vulnerability', at_init, constraint=gas_constraint)


class DetectReentrancyAdvanced(Detector):
    """
    Detector for reentrancy bugs.
    Given an optional concrete list of attacker addresses, warn on the following conditions.

    1) A _successful_ call to an attacker address (address in attacker list), or any human account address (if no list is given). With enough gas (>2300).
    2) A SSTORE after the execution of the CALL.
    3) The storage slot of the SSTORE must be used in some path to control flow
    """
    def __init__(self, addresses=None, **kwargs):
        super().__init__(**kwargs)
        # TODO Check addresses are normal accounts. Heuristics implemented here
        # assume target addresses wont execute code. i.e. won't detect a Reentrancy
        # attack in progess but only a potential attack
        self._addresses = addresses

    @property
    def _read_storage_name(self):
        return '{:s}.read_storage'.format(self.name)

    def will_open_transaction_callback(self, state, tx):
        # Reset reading log on new human transactions
        if tx.is_human():
            state.context[self._read_storage_name] = set()
            state.context['{:s}.locations'.format(self.name)] = dict()

    def did_close_transaction_callback(self, state, tx):
        world = state.platform
        #Check if it was an internal tx
        if not tx.is_human():
            # Check is the tx was successful
            if tx.result:
                # Check if gas was enough for a reentrancy attack
                if tx.gas > 2300:
                    # Check if target address is attaker controlled
                    if self._addresses is None and not world.get_code(tx.address) or self._addresses is not None and tx.address in self._addresses:
                        #that's enough. Save current location and read list
                        self._save_location_and_reads(state)

    def _save_location_and_reads(self, state):
        name = '{:s}.locations'.format(self.name)
        locations = state.context.get(name, dict)
        world = state.platform
        address = world.current_vm.address
        pc = world.current_vm.pc
        if isinstance(pc, Constant):
            pc = pc.value
        assert isinstance(pc, int)
        at_init = world.current_transaction.sort == 'CREATE'
        location = (address, pc, "Reentrancy multi-million ether bug", at_init)
        locations[location] = set(state.context[self._read_storage_name])
        state.context[name] = locations

    def _get_location_and_reads(self, state):
        name = '{:s}.locations'.format(self.name)
        locations = state.context.get(name, dict)
        return locations.items()

    def did_evm_read_storage_callback(self, state, address, offset, value):
        state.context[self._read_storage_name].add((address, offset))

    def did_evm_write_storage_callback(self, state, address, offset, value):
        # if in potential DAO check that write to storage values read before
        # the "send"
        for location, reads in self._get_location_and_reads(state):
            for address_i, offset_i in reads:
                if address_i == address:
                    if state.can_be_true(offset == offset_i):
                        self.add_finding(state, *location)


class DetectIntegerOverflow(Detector):
    """
        Detects potential overflow and underflow conditions on ADD and SUB instructions.
    """

    @staticmethod
    def _signed_sub_overflow(state, a, b):
        """
        Sign extend the value to 512 bits and check the result can be represented
         in 256. Following there is a 32 bit excerpt of this condition:
        a  -  b   -80000000 -3fffffff -00000001 +00000000 +00000001 +3fffffff +7fffffff
        +80000000    False    False    False    False     True     True     True
        +c0000001    False    False    False    False    False    False     True
        +ffffffff    False    False    False    False    False    False    False
        +00000000     True    False    False    False    False    False    False
        +00000001     True    False    False    False    False    False    False
        +3fffffff     True    False    False    False    False    False    False
        +7fffffff     True     True     True    False    False    False    False
        """
        sub = Operators.SEXTEND(a, 256, 512) - Operators.SEXTEND(b, 256, 512)
        cond = Operators.OR(sub < -(1 << 255), sub >= (1 << 255))
        return cond

    @staticmethod
    def _signed_add_overflow(state, a, b):
        """
        Sign extend the value to 512 bits and check the result can be represented
         in 256. Following there is a 32 bit excerpt of this condition:

        a  +  b   -80000000 -3fffffff -00000001 +00000000 +00000001 +3fffffff +7fffffff
        +80000000     True     True     True    False    False    False    False
        +c0000001     True    False    False    False    False    False    False
        +ffffffff     True    False    False    False    False    False    False
        +00000000    False    False    False    False    False    False    False
        +00000001    False    False    False    False    False    False     True
        +3fffffff    False    False    False    False    False    False     True
        +7fffffff    False    False    False    False     True     True     True
        """
        add = Operators.SEXTEND(a, 256, 512) + Operators.SEXTEND(b, 256, 512)
        cond = Operators.OR(add < -(1 << 255), add >= (1 << 255))
        return cond

    @staticmethod
    def _unsigned_sub_overflow(state, a, b):
        """
        Sign extend the value to 512 bits and check the result can be represented
         in 256. Following there is a 32 bit excerpt of this condition:

        a  -  b   ffffffff bfffffff 80000001 00000000 00000001 3ffffffff 7fffffff
        ffffffff     True     True     True    False     True     True     True
        bfffffff     True     True     True    False    False     True     True
        80000001     True     True     True    False    False     True     True
        00000000    False    False    False    False    False     True    False
        00000001     True    False    False    False    False     True    False
        ffffffff     True     True     True     True     True     True     True
        7fffffff     True     True     True    False    False     True    False
        """
        cond = Operators.UGT(b, a)
        return cond

    @staticmethod
    def _unsigned_add_overflow(state, a, b):
        """
        Sign extend the value to 512 bits and check the result can be represented
         in 256. Following there is a 32 bit excerpt of this condition:

        a  +  b   ffffffff bfffffff 80000001 00000000 00000001 3ffffffff 7fffffff
        ffffffff     True     True     True    False     True     True     True
        bfffffff     True     True     True    False    False     True     True
        80000001     True     True     True    False    False     True     True
        00000000    False    False    False    False    False     True    False
        00000001     True    False    False    False    False     True    False
        ffffffff     True     True     True     True     True     True     True
        7fffffff     True     True     True    False    False     True    False
        """
        add = Operators.ZEXTEND(a, 512) + Operators.ZEXTEND(b, 512)
        cond = Operators.UGE(add, 1 << 256)
        return cond

    @staticmethod
    def _signed_mul_overflow(state, a, b):
        """
        Sign extend the value to 512 bits and check the result can be represented
         in 256. Following there is a 32 bit excerpt of this condition:

        a  *  b           +00000000000000000 +00000000000000001 +0000000003fffffff +0000000007fffffff +00000000080000001 +000000000bfffffff +000000000ffffffff
        +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000
        +0000000000000001  +0000000000000000  +0000000000000001  +000000003fffffff  +000000007fffffff  +0000000080000001  +00000000bfffffff  +00000000ffffffff
        +000000003fffffff  +0000000000000000  +000000003fffffff *+0fffffff80000001 *+1fffffff40000001 *+1fffffffbfffffff *+2fffffff00000001 *+3ffffffec0000001
        +000000007fffffff  +0000000000000000  +000000007fffffff *+1fffffff40000001 *+3fffffff00000001 *+3fffffffffffffff *+5ffffffec0000001 *+7ffffffe80000001
        +0000000080000001  +0000000000000000  +0000000080000001 *+1fffffffbfffffff *+3fffffffffffffff *+4000000100000001 *+600000003fffffff *+800000007fffffff
        +00000000bfffffff  +0000000000000000  +00000000bfffffff *+2fffffff00000001 *+5ffffffec0000001 *+600000003fffffff *+8ffffffe80000001 *+bffffffe40000001
        +00000000ffffffff  +0000000000000000  +00000000ffffffff *+3ffffffec0000001 *+7ffffffe80000001 *+800000007fffffff *+bffffffe40000001 *+fffffffe00000001

        """
        mul = Operators.SEXTEND(a, 256, 512) * Operators.SEXTEND(b, 256, 512)
        cond = Operators.OR(mul < -(1 << 255), mul >= (1 << 255))
        return cond

    @staticmethod
    def _unsigned_mul_overflow(state, a, b):
        """
        Sign extend the value to 512 bits and check the result can be represented
         in 256. Following there is a 32 bit excerpt of this condition:

        a  *  b           +00000000000000000 +00000000000000001 +0000000003fffffff +0000000007fffffff +00000000080000001 +000000000bfffffff +000000000ffffffff
        +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000  +0000000000000000
        +0000000000000001  +0000000000000000  +0000000000000001  +000000003fffffff  +000000007fffffff  +0000000080000001  +00000000bfffffff  +00000000ffffffff
        +000000003fffffff  +0000000000000000  +000000003fffffff *+0fffffff80000001 *+1fffffff40000001 *+1fffffffbfffffff *+2fffffff00000001 *+3ffffffec0000001
        +000000007fffffff  +0000000000000000  +000000007fffffff *+1fffffff40000001 *+3fffffff00000001 *+3fffffffffffffff *+5ffffffec0000001 *+7ffffffe80000001
        +0000000080000001  +0000000000000000  +0000000080000001 *+1fffffffbfffffff *+3fffffffffffffff *+4000000100000001 *+600000003fffffff *+800000007fffffff
        +00000000bfffffff  +0000000000000000  +00000000bfffffff *+2fffffff00000001 *+5ffffffec0000001 *+600000003fffffff *+8ffffffe80000001 *+bffffffe40000001
        +00000000ffffffff  +0000000000000000  +00000000ffffffff *+3ffffffec0000001 *+7ffffffe80000001 *+800000007fffffff *+bffffffe40000001 *+fffffffe00000001

        """
        mul = Operators.SEXTEND(a, 256, 512) * Operators.SEXTEND(b, 256, 512)
        cond = Operators.UGE(mul, 1 << 256)
        return cond

    def _check_finding(self, state, what):
        if istainted(what, "SIGNED"):
            for taint in get_taints(what, "IOS_.*"):
                address, pc, finding, at_init, condition = self._get_location(state, taint[4:])
                if state.can_be_true(condition):
                    self.add_finding(state, address, pc, finding, at_init)
        else:
            for taint in get_taints(what, "IOU_.*"):
                address, pc, finding, at_init, condition = self._get_location(state, taint[4:])
                if state.can_be_true(condition):
                    self.add_finding(state, address, pc, finding, at_init)

    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
        vm = state.platform.current_vm
        mnemonic = instruction.semantics
        ios = False
        iou = False

        if mnemonic == 'ADD':
            ios = self._signed_add_overflow(state, *arguments)
            iou = self._unsigned_add_overflow(state, *arguments)
        elif mnemonic == 'MUL':
            ios = self._signed_mul_overflow(state, *arguments)
            iou = self._unsigned_mul_overflow(state, *arguments)
        elif mnemonic == 'SUB':
            ios = self._signed_sub_overflow(state, *arguments)
            iou = self._unsigned_sub_overflow(state, *arguments)
        elif mnemonic == 'SSTORE':
            # If an overflowded value is stored in the storage then it is a finding
            where, what = arguments
            self._check_finding(state, what)
        elif mnemonic == 'RETURN':
            world = state.platform
            if world.current_transaction.is_human():
                # If an overflowded value is returned to a human
                offset, size = arguments
                data = world.current_vm.read_buffer(offset, size)
                self._check_finding(state, data)

        if mnemonic in ('SLT', 'SGT', 'SDIV', 'SMOD'):
            result = taint_with(result, "SIGNED")
            vm.change_last_result(result)
        if state.can_be_true(ios):
            id_val = self._save_current_location(state, "Signed integer overflow at %s instruction" % mnemonic, ios)
            result = taint_with(result, "IOS_{:s}".format(id_val))
            vm.change_last_result(result)
        if state.can_be_true(iou):
            id_val = self._save_current_location(state, "Unsigned integer overflow at %s instruction" % mnemonic, iou)
            result = taint_with(result, "IOU_{:s}".format(id_val))
            vm.change_last_result(result)


class DetectUnusedRetVal(Detector):
    """ Detects unused return value from internal transactions """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._stack_name = '{:s}.stack'.format(self.name)

    def _add_retval_taint(self, state, taint):
        taints = state.context[self._stack_name][-1]
        taints.add(taint)
        state.context[self._stack_name][-1] = taints

    def _remove_retval_taint(self, state, taint):
        taints = state.context[self._stack_name][-1]
        if taint in taints:
            taints.remove(taint)
            state.context[self._stack_name][-1] = taints

    def _get_retval_taints(self, state):
        return state.context[self._stack_name][-1]

    def will_open_transaction_callback(self, state, tx):
        # Reset reading log on new human transactions
        if tx.is_human():
            state.context[self._stack_name] = []
        state.context[self._stack_name].append(set())

    def did_close_transaction_callback(self, state, tx):
        world = state.platform
        # Check that all retvals were used in control flow
        for taint in self._get_retval_taints(state):
            id_val = taint[7:]
            address, pc, finding, at_init, condition = self._get_location(state, id_val)
            if state.can_be_true(condition):
                self.add_finding(state, address, pc, finding, at_init)

        state.context[self._stack_name].pop()

    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
        world = state.platform
        mnemonic = instruction.semantics
        current_vm = world.current_vm
        if instruction.is_starttx:
            # A transactional instruction just returned so we add a taint to result
            # and add that taint to the set
            id_val = self._save_current_location(state, "Returned value at {:s} instruction is not used".format(mnemonic))
            taint = "RETVAL_{:s}".format(id_val)
            current_vm.change_last_result(taint_with(result, taint))
            self._add_retval_taint(state, taint)
        elif mnemonic == 'JUMPI':
            dest, cond = arguments
            for used_taint in get_taints(cond, "RETVAL_.*"):
                self._remove_retval_taint(state, used_taint)


class DetectDelegatecall(Detector):
    '''
        Detects DELEGATECALLs to controlled addresses and or with controlled function id.
        This detector finds and reports on any delegatecall instruction any the following propositions are hold:
            * the destination address can be controlled by the caller
            * the first 4 bytes of the calldata are controlled by the caller
    '''

    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        world = state.platform
        mnemonic = instruction.semantics
        current_vm = world.current_vm
        # If it executed a DELEGATECALL
        # TODO: Check the transaction was success
        # if blockchain.last_transaction.return_value:
        # TODO: check if any of the potential target addresses has code
        # if not any( world.get_code, possible_addresses):
        if mnemonic == 'DELEGATECALL':
            gas, address, in_offset, in_size, out_offset, out_size = arguments
            if issymbolic(address):
                possible_addresses = state.solve_n(address, 2)
                if len(possible_addresses) > 1:
                    self.add_finding_here(state, "Delegatecall to user controlled address")

            calldata = world.current_vm.read_buffer(in_offset, in_size)
            func_id = calldata[:4]
            if issymbolic(func_id):
                possible_func_ids = state.solve_n(func_id, 2)
                if len(possible_func_ids) > 1:
                    self.add_finding_here(state, "Delegatecall to user controlled function")


class DetectUninitializedMemory(Detector):
    """
        Detects uses of uninitialized memory
    """

    def did_evm_read_memory_callback(self, state, offset, value):
        initialized_memory = state.context.get('{:s}.initialized_memory'.format(self.name), set())
        cbu = True  # Can be unknown
        current_contract = state.platform.current_vm.address
        for known_contract, known_offset in initialized_memory:
            if current_contract == known_contract:
                cbu = Operators.AND(cbu, offset != known_offset)
        if state.can_be_true(cbu):
            self.add_finding_here(state, "Potentially reading uninitialized memory at instruction (address: %r, offset %r)" % (current_contract, offset))

    def did_evm_write_memory_callback(self, state, offset, value):
        current_contract = state.platform.current_vm.address

        # concrete or symbolic write
        state.context.setdefault('{:s}.initialized_memory'.format(self.name), set()).add((current_contract, offset))


class DetectUninitializedStorage(Detector):
    """
        Detects uses of uninitialized storage
    """

    def did_evm_read_storage_callback(self, state, address, offset, value):
        if not state.can_be_true(value != 0):
            # Not initialized memory should be zero
            return
        # check if offset is known
        cbu = True  # Can be unknown
        context_name = '{:s}.initialized_storage'.format(self.name)
        for known_address, known_offset in state.context.get(context_name, ()):
            cbu = Operators.AND(cbu, Operators.OR(address != known_address, offset != known_offset))

        if state.can_be_true(cbu):
            self.add_finding_here(state, "Potentially reading uninitialized storage")

    def did_evm_write_storage_callback(self, state, address, offset, value):
        # concrete or symbolic write
        state.context.setdefault('{:s}.initialized_storage'.format(self.name), set()).add((address, offset))


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


class SolidityMetadata(object):
    def __init__(self, name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings):
        """ Contract metadata for Solidity-based contracts """
        self.name = name
        if isinstance(source_code, bytes):
            source_code = source_code.decode()
        self.source_code = source_code
        self._init_bytecode = init_bytecode
        self._runtime_bytecode = runtime_bytecode
        self._functions = hashes.keys()
        self.abi = {item.get('name', '{fallback}'): item for item in abi}
        self.warnings = warnings
        self.srcmap_runtime = self.__build_source_map(self.runtime_bytecode, srcmap_runtime)
        self.srcmap = self.__build_source_map(self.init_bytecode, srcmap)

    def get_constructor_arguments(self):
        for fun in self.abi.values():
            if fun['type'] == 'constructor':
                constructor_inputs = fun['inputs']
                break
        else:
            constructor_inputs = ()

        def process(spec):
            if spec['type'].startswith('tuple'):
                types = []
                for component in spec['components']:
                    types.append(process(component))
                return '({}){:s}'.format(','.join(types), spec['type'][5:])
            else:
                return spec['type']
        inputs = {'components': constructor_inputs, 'type': 'tuple'}
        return process(inputs)

    def add_function(self, method_name_and_signature):
        if not isinstance(method_name_and_signature, str):
            raise ValueError("method_name_and_signature needs to be a string")
        #TODO: use re, and check it's sane
        name = method_name_and_signature.split('(')[0]
        if name in self.abi:
            raise EthereumError("Function already defined")
        hsh = ABI.function_selector(method_name_and_signature)
        self._functions.add(method_name_and_signature)

        input_types = method_name_and_signature.split('(')[1].split(')')[0].split(',')
        output_types = method_name_and_signature.split(')')[1].split(',')
        self.abi[name] = {'inputs': [{'type': ty} for ty in input_types],
                          'name': name,
                          'outputs': [{'type': ty} for ty in output_types]}

    @staticmethod
    def _without_metadata(bytecode):
        end = None
        if bytecode[-43: -34] == b'\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
                and bytecode[-2:] == b'\x00\x29':
            end = -9 - 32 - 2  # Size of metadata at the end of most contracts
        return bytecode[:end]

    def __build_source_map(self, bytecode, srcmap):
        # https://solidity.readthedocs.io/en/develop/miscellaneous.html#source-mappings
        new_srcmap = {}
        bytecode = self._without_metadata(bytecode)

        asm_offset = 0
        asm_pos = 0
        md = dict(enumerate(srcmap[asm_pos].split(':')))
        byte_offset = int(md.get(0, 0))  # is the byte-offset to the start of the range in the source file
        source_len = int(md.get(1, 0))  # is the length of the source range in bytes
        file_index = int(md.get(2, 0))  # is the source index over sourceList
        jump_type = md.get(3, None)  # this can be either i, o or - signifying whether a jump instruction goes into a function, returns from a function or is a regular jump as part of e.g. a loop

        pos_to_offset = {}
        for i in EVMAsm.disassemble_all(bytecode):
            pos_to_offset[asm_pos] = asm_offset
            asm_pos += 1
            asm_offset += i.size

        for asm_pos, md in enumerate(srcmap):
            if len(md):
                d = {p: k for p, k in enumerate(md.split(':')) if k}

                byte_offset = int(d.get(0, byte_offset))
                source_len = int(d.get(1, source_len))
                file_index = int(d.get(2, file_index))
                jump_type = d.get(3, jump_type)

            new_srcmap[pos_to_offset[asm_pos]] = (byte_offset, source_len, file_index, jump_type)

        return new_srcmap

    @property
    def runtime_bytecode(self):
        # Removes metadata from the tail of bytecode
        return self._without_metadata(self._runtime_bytecode)

    @property
    def init_bytecode(self):
        # Removes metadata from the tail of bytecode
        return self._without_metadata(self._init_bytecode)

    def get_source_for(self, asm_offset, runtime=True):
        """ Solidity source code snippet related to `asm_pos` evm bytecode offset.
            If runtime is False, initialization bytecode source map is used
        """
        srcmap = self.get_srcmap(runtime)

        try:
            beg, size, _, _ = srcmap[asm_offset]
        except KeyError:
            #asm_offset pointing outside the known bytecode
            return ''

        output = ''
        nl = self.source_code[:beg].count('\n')
        snippet = self.source_code[beg:beg + size]
        for l in snippet.split('\n'):
            output += '    %s  %s\n' % (nl, l)
            nl += 1
        return output

    def get_srcmap(self, runtime=True):
        return self.srcmap_runtime if runtime else self.srcmap

    @property
    def signatures(self):
        return dict(((self.get_hash(f), f) for f in self._functions))

    def get_abi(self, hsh):
        func_name = self.get_func_name(hsh)
        default_fallback_abi = {'stateMutability': 'nonpayable', 'payable': False, 'type': 'fallback'}
        return self.abi.get(func_name, default_fallback_abi)

    def get_func_argument_types(self, hsh):
        abi = self.get_abi(hsh)
        return '(' + ','.join(x['type'] for x in abi.get('inputs', [])) + ')'

    def get_func_return_types(self, hsh):
        abi = self.get_abi(hsh)
        return '(' + ','.join(x['type'] for x in abi.get('outputs', [])) + ')'

    def get_func_name(self, hsh):
        signature = self.signatures.get(hsh, '{fallback}()')
        return signature.split('(')[0]

    def get_func_signature(self, hsh):
        return self.signatures.get(hsh)

    def get_hash(self, method_name_and_signature):
        #helper
        return ABI.function_selector(method_name_and_signature)

    @property
    def functions(self):
        return tuple(self._functions) + ('{fallback}()',)

    @property
    def hashes(self):
        # \x00\x00\x00\x00 corresponds to {fallback}()
        return tuple(map(self.get_hash, self._functions)) + (b'\x00\x00\x00\x00',)

    def parse_tx(self, calldata, returndata=None):
        if returndata is None:
            returndata = bytes()
        if not isinstance(calldata, (bytes, bytearray)):
            raise ValueError("calldata must be a concrete array")
        if not isinstance(returndata, (bytes, bytearray)):
            raise ValueError("returndata must be a concrete array")
        calldata = bytes(calldata)
        returndata = bytes(returndata)
        function_id = calldata[:4]
        signature = self.get_func_signature(function_id)
        function_name = self.get_func_name(function_id)
        if signature:
            _, arguments = ABI.deserialize(signature, calldata)
        else:
            arguments = (calldata,)

        arguments_str = ', '.join(map(str, arguments))
        return_value = None
        if returndata:
            ret_types = self.get_func_return_types(function_id)
            return_value = ABI.deserialize(ret_types, returndata)  # function return
            return f'{function_name}({arguments_str}) -> {return_value}'
        else:
            return f'{function_name}({arguments_str})'


class ABI(object):
    """
        This class contains methods to handle the ABI.
        The Application Binary Interface is the standard way to interact with
        contracts in the Ethereum ecosystem, both from outside the blockchain
        and for contract-to-contract interaction.

    """
    @staticmethod
    def _type_size(ty):
        """ Calculate `static` type size """
        if ty[0] in ('int', 'uint', 'bytesM', 'function'):
            return 32
        elif ty[0] in ('tuple'):
            result = 0
            for ty_i in ty[1]:
                result += ABI._type_size(ty_i)
            return result
        elif ty[0] in ('array'):
            rep = ty[1]
            result = 32  # offset link
            return result
        elif ty[0] in ('bytes', 'string'):
            result = 32  # offset link
            return result
        raise ValueError

    @staticmethod
    def function_call(type_spec, *args):
        """
        Build transaction data from function signature and arguments
        """
        m = re.match(r"(?P<name>[a-zA-Z_][a-zA-Z_0-9]*)(?P<type>\(.*\))", type_spec)
        if not m:
            raise EthereumError("Function signature expected")

        result = ABI.function_selector(type_spec)  # Funcid
        result += ABI.serialize(m.group('type'), *args)
        return result

    @staticmethod
    def serialize(ty, *value, **kwargs):
        """
        Serialize value using type specification in ty.
        ABI.serialize('int256', 1000)
        ABI.serialize('(int, int256)', 1000, 2000)
        """
        try:
            parsed_ty = abitypes.parse(ty)
        except Exception as e:
            # Catch and rebrand parsing errors
            raise EthereumError(str(e))

        if parsed_ty[0] != 'tuple':
            if len(value) > 1:
                raise ValueError
            value = value[0]

        result, dyn_result = ABI._serialize(parsed_ty, value)
        return result + dyn_result

    @staticmethod
    def _serialize(ty, value, dyn_offset=None):
        if dyn_offset is None:
            dyn_offset = ABI._type_size(ty)

        result = bytearray()
        dyn_result = bytearray()

        if ty[0] == 'int':
            result += ABI._serialize_int(value, size=ty[1] // 8, padding=32 - ty[1] // 8)
        elif ty[0] == 'uint':
            result += ABI._serialize_uint(value, size=ty[1] // 8, padding=32 - ty[1] // 8)
        elif ty[0] == 'bytesM':
            nbytes = ty[1]
            if len(value) > nbytes:
                raise EthereumError('bytesM: value length exceeds size of bytes{} type'.format(nbytes))
            result += ABI._serialize_bytes(value)
        elif ty[0] in ('bytes', 'string'):
            result += ABI._serialize_uint(dyn_offset)
            dyn_result += ABI._serialize_uint(len(value))
            dyn_result += ABI._serialize_bytes(value)
        elif ty[0] == 'function':
            result = ABI._serialize_uint(value[0], 20)
            result += value[1] + bytearray('\0' * 8)
            assert len(result) == 32
        elif ty[0] == 'tuple':
            sub_result, sub_dyn_result = ABI._serialize_tuple(ty[1], value, dyn_offset)
            result += sub_result
            dyn_result += sub_dyn_result
        elif ty[0] == 'array':
            rep = ty[1]
            base_type = ty[2]
            sub_result, sub_dyn_result = ABI._serialize_array(rep, base_type, value, dyn_offset)
            result += sub_result
            dyn_result += sub_dyn_result

        assert len(result) == ABI._type_size(ty)
        return result, dyn_result

    @staticmethod
    def _serialize_bytes(value):
        """
        Serializes the value and pads to multiple of 32 bytes

        :param value:
        :type value: bytearray or Array
        """
        return value + bytearray(b'\x00' * (32 - len(value)))

    @staticmethod
    def _serialize_tuple(types, value, dyn_offset=None):
        result = bytearray()
        dyn_result = bytearray()
        for ty_i, value_i in zip(types, value):
            result_i, dyn_result_i = ABI._serialize(ty_i, value_i, dyn_offset + len(dyn_result))
            result += result_i
            dyn_result += dyn_result_i
        return result, dyn_result

    @staticmethod
    def _serialize_array(rep, base_type, value, dyn_offset=None):
        result = ABI._serialize_uint(dyn_offset)
        dyn_result = bytearray()

        sub_result = bytearray()
        sub_dyn_result = bytearray()

        if rep is not None and len(value) != rep:
            raise ValueError("More reps than values")
        sub_result += ABI._serialize_uint(len(value))

        for value_i in value:
            result_i, dyn_result_i = ABI._serialize(base_type, value_i, dyn_offset + len(dyn_result))
            sub_result += result_i
            sub_dyn_result += dyn_result_i

        dyn_result += sub_result
        dyn_result += sub_dyn_result
        return result, dyn_result

    @staticmethod
    def function_selector(method_name_and_signature):
        """
        Makes a function hash id from a method signature
        """
        s = sha3.keccak_256()
        s.update(method_name_and_signature.encode())
        return bytes(s.digest()[:4])

    @staticmethod
    def deserialize(type_spec, data):
        try:
            if isinstance(data, str):
                data = bytearray(data.encode())
            elif isinstance(data, bytes):
                data = bytearray(data)
            assert isinstance(data, (bytearray, Array))

            m = re.match(r"(?P<name>[a-zA-Z_0-9]+)(?P<type>\(.*\))", type_spec)
            if m and m.group('name'):
                # Type has function name. Lets take the function id from the data
                # This does not check that the encoded func_id is valid
                # func_id = ABI.function_selector(type_spec)
                result = (data[:4],)
                ty = m.group('type')
                result += (ABI._deserialize(abitypes.parse(ty), data[4:]),)
            else:
                # No function name, just types
                ty = type_spec
                result = ABI._deserialize(abitypes.parse(ty), data)
            return result
        except Exception as e:
            raise EthereumError("Error {} deserializing type {:s}".format(str(e), type_spec))

    @staticmethod
    def _deserialize(ty, buf, offset=0):
        assert isinstance(buf, (bytearray, Array))
        result = None
        if ty[0] == 'int':
            result = ABI._deserialize_int(buf[offset:offset + 32], nbytes=ty[1] // 8)
        elif ty[0] == 'uint':
            result = ABI._deserialize_uint(buf[offset:offset + 32], nbytes=ty[1] // 8)
        elif ty[0] == 'bytesM':
            result = buf[offset:offset + ty[1]]
        elif ty[0] == 'function':
            address = Operators.ZEXTEND(ABI._readBE(buf[offset:offset + 20], 20, padding=False), 256)
            func_id = buf[offset + 20:offset + 24]
            result = (address, func_id)
        elif ty[0] in ('bytes', 'string'):
            dyn_offset = ABI._deserialize_int(buf[offset:offset + 32])
            size = ABI._deserialize_int(buf[dyn_offset:dyn_offset + 32])
            result = buf[dyn_offset + 32:dyn_offset + 32 + size]
        elif ty[0] in ('tuple'):
            result = ()
            current_off = 0
            for ty_i in ty[1]:
                result += (ABI._deserialize(ty_i, buf, offset), )
                offset += ABI._type_size(ty_i)
        elif ty[0] in ('array'):
            result = []
            dyn_offset = ABI._deserialize_int(buf[offset:offset + 32])
            rep = ty[1]
            ty_size = ABI._type_size(ty[2])
            if rep is None:
                rep = ABI._deserialize_int(buf[dyn_offset:dyn_offset + 32])
                dyn_offset += 32
            for _ in range(rep):
                result.append(ABI._deserialize(ty[2], buf, dyn_offset))
                dyn_offset += ty_size
        else:
            raise NotImplemented

        return result

    @staticmethod
    def _serialize_uint(value, size=32, padding=0):
        """
        Translates a python integral or a BitVec into a 32 byte string, MSB first
        """
        if size <= 0 and size > 32:
            raise ValueError

        if not isinstance(value, (int, BitVec, EVMAccount)):
            raise ValueError
        if issymbolic(value):
            # FIXME This temporary array variable should be obtained from a specific constraint store
            bytes = ArrayVariable(index_bits=256, index_max=32, value_bits=8, name='temp{}'.format(uuid.uuid1()))
            value = Operators.ZEXTEND(value, size * 8)
            bytes = ArrayProxy(bytes.write_BE(padding, value, size))
        else:
            value = int(value)
            bytes = bytearray()
            for _ in range(padding):
                bytes.append(0)
            for position in reversed(range(size)):
                bytes.append(Operators.EXTRACT(value, position * 8, 8))
        assert len(bytes) == size + padding
        return bytes

    @staticmethod
    def _serialize_int(value, size=32, padding=0):
        """
        Translates a signed python integral or a BitVec into a 32 byte string, MSB first
        """
        if size <= 0 and size > 32:
            raise ValueError
        if not isinstance(value, (int, BitVec)):
            raise ValueError
        if issymbolic(value):
            buf = ArrayVariable(index_bits=256, index_max=32, value_bits=8, name='temp{}'.format(uuid.uuid1()))
            value = Operators.SEXTEND(value, value.size, size * 8)
            buf = ArrayProxy(buf.write_BE(padding, value, size))
        else:
            value = int(value)
            buf = bytearray()
            for _ in range(padding):
                buf.append(0)

            for position in reversed(range(size)):
                buf.append(Operators.EXTRACT(value, position * 8, 8))
        return buf

    @staticmethod
    def _readBE(data, nbytes, padding=True):
        if padding:
            pos = 32 - nbytes
            size = 32
        else:
            pos = 0
            size = nbytes

        values = []
        while pos < size:
            if pos >= len(data):
                values.append(0)
            else:
                values.append(data[pos])
            pos += 1
        return Operators.CONCAT(nbytes * 8, *values)

    @staticmethod
    def _deserialize_uint(data, nbytes=32, padding=0):
        """
        Read a `nbytes` bytes long big endian unsigned integer from `data` starting at `offset`

        :param data: sliceable buffer; symbolic buffer of Eth ABI encoded data
        :param nbytes: number of bytes to read starting from least significant byte
        :rtype: int or Expression
        """
        assert isinstance(data, (bytearray, Array))
        value = ABI._readBE(data, nbytes)
        value = Operators.ZEXTEND(value, (nbytes + padding) * 8)
        return value

    @staticmethod
    def _deserialize_int(data, nbytes=32, padding=0):
        """
        Read a `nbytes` bytes long big endian signed integer from `data` starting at `offset`

        :param data: sliceable buffer; symbolic buffer of Eth ABI encoded data
        :param nbytes: number of bytes to read starting from least significant byte
        :rtype: int or Expression
        """
        assert isinstance(data, (bytearray, Array))
        value = ABI._readBE(data, nbytes)
        value = Operators.SEXTEND(value, nbytes * 8, (nbytes + padding) * 8)
        if not issymbolic(value):
            # sign bit on
            if value & (1 << (nbytes * 8 - 1)):
                value = -(((~value) + 1) & ((1 << (nbytes * 8)) - 1))
        return value


class EVMAccount(object):
    def __init__(self, address=None, manticore=None, name=None):
        """ Encapsulates an account.

            :param address: the address of this account
            :type address: 160 bit long integer
            :param manticore: the controlling Manticore

        """
        self._manticore = manticore
        self._address = address
        self._name = name

    def __eq__(self, other):
        if isinstance(other, int):
            return self._address == other
        if isinstance(self, EVMAccount):
            return self._address == other._address
        return super().__eq__(other)

    @property
    def name(self):
        return self._name

    @property
    def address(self):
        return self._address

    def __int__(self):
        return self._address

    def __str__(self):
        return str(self._address)


class EVMContract(EVMAccount):
    """ An EVM account

        Note: The private methods of this class begin with a double underscore to
        avoid function name collisions with Solidity functions that begin with
        a single underscore
    """

    def __init__(self, default_caller=None, **kwargs):
        """ Encapsulates a contract account.
            :param default_caller: the default caller address for any transaction

        """
        super().__init__(**kwargs)
        self._default_caller = default_caller
        self._hashes = None

    def add_function(self, signature):
        func_id = ABI.function_selector(signature)
        func_name = str(signature.split('(')[0])
        if func_name.startswith('__') or func_name in {'add_function', 'address', 'name'}:
            # TODO(mark): is this actually true? is there anything actually wrong with a solidity name beginning w/ an underscore?
            raise EthereumError("Function name ({}) is internally reserved".format(func_name))
        if func_name in self._hashes:
            self._hashes[func_name].append((signature, func_id))
            return
        if func_id in {h[1] for names in self._hashes.values() for h in names}:
            raise EthereumError("A function with the same hash as {} is already defined".format(func_name))
        self._hashes[func_name] = [(signature, func_id)]

    def __null_func(self):
        pass

    def __init_hashes(self):
        #initializes self._hashes lazy
        if self._hashes is None and self._manticore is not None:
            self._hashes = {}
            md = self._manticore.get_metadata(self._address)
            if md is not None:
                for signature in md.functions:
                    self.add_function(signature)
            # It was successful, no need to re-run. _init_hashes disabled
            self.__init_hashes = self.__null_func

    def __getattribute__(self, name):
        """ If this is a contract account of which we know the functions hashes,
            this will build the transaction for the function call.

            Example use::

                #call funtion `add` on contract_account with argument `1000`
                contract_account.add(1000)

        """
        if not name.startswith('_'):
            self.__init_hashes()
            if self._hashes is not None and name in self._hashes.keys():
                def f(*args, signature: Optional[str]=None, caller=None, value=0, **kwargs):
                    try:
                        if signature:
                            if f'{name}{signature}' not in {h[0] for names in self._hashes.values() for h in names}:
                                raise EthereumError(
                                    f'Function: `{name}` has no such signature`\n'
                                    f'Known signatures: {[x[0][len(name):] for x in self._hashes[name]]}')

                            tx_data = ABI.function_call(f'{name}{signature}', *args)
                        else:
                            if len(self._hashes[name]) > 1:
                                sig = self._hashes[name][0][0][len(name):]
                                raise EthereumError(
                                    f'Function: `{name}` has multiple signatures but `signature` is not '
                                    f'defined! Example: `account.{name}(..., signature="{sig}")`\n'
                                    f'Known signatures: {[x[0][len(name):] for x in self._hashes[name]]}')

                            tx_data = ABI.function_call(str(self._hashes[name][0][0]), *args)
                    except KeyError as e:
                        raise e

                    if caller is None:
                        caller = self._default_caller

                    self._manticore.transaction(caller=caller,
                                                address=self._address,
                                                value=value,
                                                data=tx_data)
                return f

        return object.__getattribute__(self, name)


class ManticoreEVM(Manticore):
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

    def make_symbolic_buffer(self, size, name=None):
        """ Creates a symbolic buffer of size bytes to be used in transactions.
            You can operate on it normally and add constrains to manticore.constraints
            via manticore.constrain(constraint_expression)

            Example use::

                symbolic_data = m.make_symbolic_buffer(320)
                m.constrain(symbolic_data[0] == 0x65)
                m.transaction(caller=attacker_account,
                                address=contract_account,
                                data=symbolic_data,
                                value=100000 )
        """
        avoid_collisions = False
        if name is None:
            name = 'TXBUFFER'
            avoid_collisions = True
        return self.constraints.new_array(index_bits=256, name=name, index_max=size, value_bits=8, taint=frozenset(), avoid_collisions=avoid_collisions)

    def make_symbolic_value(self, nbits=256, name=None):
        """ Creates a symbolic value, normally a uint256, to be used in transactions.
            You can operate on it normally and add constrains to manticore.constraints
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
    def _run_solc(source_file, solc_bin=None, solc_remaps=[]):
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

        #shorten the path size so library placeholders wont fail.
        #solc path search is a mess #fixme
        #https://solidity.readthedocs.io/en/latest/layout-of-source-files.html
        current_folder = os.getcwd()
        abs_filename = os.path.abspath(source_file.name)
        working_folder, filename = os.path.split(abs_filename)

        solc_invocation = [
            solc,
        ]
        solc_invocation.extend(solc_remaps)
        solc_invocation.extend([
            '--combined-json', 'abi,srcmap,srcmap-runtime,bin,hashes,bin-runtime',
            '--allow-paths', '.',
            filename
        ])

        p = Popen(solc_invocation, stdout=PIPE, stderr=PIPE, cwd=working_folder)
        stdout, stderr = p.communicate()
        try:
            return json.loads(stdout.decode()), stderr.decode()
        except ValueError:
            raise EthereumError('Solidity compilation error:\n\n{}'.format(stderr.decode()))

    @staticmethod
    def _compile(source_code, contract_name, libraries=None, solc_bin=None, solc_remaps=[]):
        """ Compile a Solidity contract, used internally

            :param source_code: solidity source as either a string or a file handle
            :param contract_name: a string with the name of the contract to analyze
            :param libraries: an itemizable of pairs (library_name, address)
            :param solc_bin: path to solc binary
            :param solc_remaps: solc import remaps
            :return: name, source_code, bytecode, srcmap, srcmap_runtime, hashes
            :return: name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings
        """

        if isinstance(source_code, str):
            with tempfile.NamedTemporaryFile('w+') as temp:
                temp.write(source_code)
                temp.flush()
                output, warnings = ManticoreEVM._run_solc(temp, solc_bin, solc_remaps)
        elif isinstance(source_code, io.IOBase):
            output, warnings = ManticoreEVM._run_solc(source_code, solc_bin, solc_remaps)
            source_code.seek(0)
            source_code = source_code.read()
        else:
            raise TypeError

        contracts = output.get('contracts', [])
        if len(contracts) != 1 and contract_name is None:
            raise EthereumError('Solidity file must contain exactly one contract or you must use contract parameter to specify which one.')

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

    def __init__(self, procs=10, **kwargs):
        """ A Manticore EVM manager
            :param int procs: number of workers to use in the exploration
        """
        self._accounts = dict()
        self._serializer = PickleSerializer()

        self._config_procs = procs
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints, initial_timestamp=1524785992)
        initial_state = State(constraints, world)
        super().__init__(initial_state, **kwargs)

        self.constraints = ConstraintSet()
        self.detectors = {}
        self.metadata = {}

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
        return self.get_world(None)

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
        """ Manually revice a states by state_id.
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

    def make_symbolic_arguments(self, types):
        """
            Make a reasonable serialization of the symbolic argument types
        """
        # FIXME this is more naive than reasonable.
        return ABI.deserialize(types, self.make_symbolic_buffer(32, name="INITARGS"))

    def solidity_create_contract(self, source_code, owner, name=None, contract_name=None, libraries=None, balance=0, address=None, args=(), solc_bin=None, solc_remaps=[]):
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
                compile_results = self._compile(source_code, contract_name_i, libraries=deps, solc_bin=solc_bin, solc_remaps=solc_remaps)
                md = SolidityMetadata(*compile_results)
                if contract_name_i == contract_name:
                    constructor_types = md.get_constructor_arguments()
                    if args is None:
                        args = self.make_symbolic_arguments(constructor_types)
                    contract_account = self.create_contract(owner=owner,
                                                            balance=balance,
                                                            address=address,
                                                            init=md._init_bytecode + ABI.serialize(constructor_types, *args),
                                                            name=name)
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

    def create_contract(self, owner, balance=0, address=None, init=None, name=None, gas=21000):
        """ Creates a contract

            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transferred on creation
            :type balance: int or SValue
            :param int address: the address for the new contract (optional)
            :param str init: initializing evm bytecode and arguments
            :param str name: a uniq name for reference
            :param gas: gas budget for the creation/inititialization of the contract
            :rtype: EVMAccount
        """
        if not self.count_running_states():
            raise NoAliveStates

        if address is not None and address in map(int, self.accounts.values()):
            # Address already used
            raise EthereumError("Address already used")

        # Let just choose the address ourself. This is not yellow paper material
        if address is None:
            address = self.new_address()

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

    def new_address(self):
        """ Create a fresh 160bit address """
        new_address = random.randint(100, pow(2, 160))
        if new_address in map(int, self.accounts.values()):
            return self.new_address()
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
        # Let just choose the address ourself. This is not yellow paper material
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
                raise EthereumError("This is bad. It should not be a pending transaction")

            if address in world.accounts:
                # Address already used
                raise EthereumError("This is bad. Same address used for different contracts in different states")
            world.create_account(address, balance, code=code, storage=None)

        self._accounts[name] = EVMAccount(address, manticore=self, name=name)
        return self.accounts[name]

    def _migrate_tx_expressions(self, state, caller, address, value, data):
            # Copy global constraints into each state.
            # We should somehow remember what has been copied to each state
            # In a second transaction we should only add new constraints.
            # And actually only constraints related to whateverwe are using in
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
                if isinstance(data, ArrayProxy):  # FIXME is this necesary here?
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
            raise EthereumError("code bad type")

        # Check types
        if not isinstance(address, (int, BitVec)):
            raise EthereumError("Caller invalid type")

        if not isinstance(value, (int, BitVec)):
            raise EthereumError("Value invalid type")

        if not isinstance(address, (int, BitVec)):
            raise EthereumError("address invalid type")

        if not isinstance(price, int):
            raise EthereumError("Price invalid type")

        # Check argument consistency and set defaults ...
        if sort not in ('CREATE', 'CALL'):
            raise ValueError('unsupported transaction type')

        if sort == 'CREATE':
            #let's choose an address here for now #NOTYELLOW
            if address is None:
                address = self.new_address()

            # When creating data is the init_bytecode + arguments
            if len(data) == 0:
                raise EthereumError("An initialization bytecode is needed for a CREATE")

        assert address is not None
        assert caller is not None

        # Transactions (as everything else) needs at least one running state
        if not self.count_running_states():
            raise NoAliveStates

        # To avoid going full crazy we maintain a global list of addresses
        for state in self.running_states:
            world = state.platform

            if '_pending_transaction' in state.context:
                raise EthereumError("This is bad. It should not be a pending transaction")

            # Migrate any expression to state specific constraint set
            caller, address, value, data = self._migrate_tx_expressions(state, caller, address, value, data)

            # Different states may CREATE a different set of accounts. Accounts
            # that were crated by a human have the same address in all states.
            # This diverges from the yellow paper but at least we check that we
            # are not trying to create an already used address here
            if sort == 'CREATE':
                if address in world.accounts:
                    # Address already used
                    raise EthereumError("This is bad. Same address used for different contracts in different states")

            state.context['_pending_transaction'] = (sort, caller, address, value, data, gaslimit, price)

        # run over potentially several states and
        # generating potentially several others
        self.run(procs=self._config_procs)

        return address

    def multi_tx_analysis(self, solidity_filename, contract_name=None, tx_limit=None, tx_use_coverage=True, tx_send_ether=True, tx_account="attacker", args=None):
        owner_account = self.create_account(balance=1000, name='owner')
        attacker_account = self.create_account(balance=1000, name='attacker')

        # Pretty print
        logger.info("Starting symbolic create contract")

        with open(solidity_filename) as f:
            contract_account = self.solidity_create_contract(f, contract_name=contract_name, owner=owner_account, args=args)

        if tx_account == "attacker":
            tx_account = [attacker_account]
        elif tx_account == "owner":
            tx_account = [owner_account]
        elif tx_account == "combo1":
            tx_account = [owner_account, attacker_account]
        else:
            raise EthereumError('The account to perform the symbolic exploration of the contract should be "attacker", "owner" or "combo1"')

        if contract_account is None:
            logger.info("Failed to create contract. Exception in constructor")
            self.finalize()
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
                self.transaction(caller=tx_account[min(tx_no, len(tx_account) - 1)],
                                 address=contract_account,
                                 data=symbolic_data,
                                 value=value,
                                 gas=2100000)
                logger.info("%d alive states, %d terminated states", self.count_running_states(), self.count_terminated_states())
            except NoAliveStates:
                break

            # Check if the maximun number of tx was reached
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
            # there is no states added to the executor queue
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
            if self.count_running_states() == 1:
                #Get the ID of the single running state
                state_id = self._running_state_ids[0]
            else:
                raise EthereumError("More than one state running, you must specify state id.")

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
                known_sha3.append((data_concrete, data_hash))
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
                raise TerminateState("There is not matching sha3 pair, bailing out")

            #send knwon hashes to evm
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
            Every time a state finishes executing last transaction we save it in
            our private list
        """
        if str(e) == 'Abandoned state':
            #do nothing
            return
        world = state.platform
        state.context['last_exception'] = e
        e.testcase = False  # Do not generate a testcase file

        if not world.all_transactions:
            logger.debug("Something was wrong. Search terminated in the middle of an ongoing tx")
            self.save(state, final=True)
            return

        tx = world.all_transactions[-1]

        #is we initiated the Tx we need process the outcome for now.
        #Fixme incomplete.
        if tx.is_human():
            if tx.sort == 'CREATE':
                if tx.result == 'RETURN':
                    world.set_code(tx.address, tx.return_data)
                else:
                    world.delete_account(tx.address)
        else:
            logger.info("Manticore exception. State should be terminated only at the end of the human transaction")

        #Human tx that ends in this wont modify the storage so finalize and
        # generate a testcase. FIXME This should be configurable as REVERT and
        # THROWit actually changes the balance and nonce? of some accounts
        if tx.result in {'SELFDESTRUCT', 'REVERT', 'THROW', 'TXERROR'}:
            self.save(state, final=True)
        elif tx.result in {'RETURN', 'STOP'}:
            # if not a revert we save the state for further transactioning
            self.save(state)  # Add to running states
        else:
            logger.debug("Exception in state. Discarding it")

    #Callbacks
    def _load_state_callback(self, state, state_id):
        """ INTERNAL USE
            When a state was just loaded from stoage we do the pending transaction
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

    def get_metadata(self, address):
        """ Gets the solidity metadata for address.
            This is available only if address is a contract created from solidity
        """
        return self.metadata.get(int(address))

    def register_detector(self, d):
        if not isinstance(d, Detector):
            raise EthereumError("Not a Detector")
        if d.name in self.detectors:
            raise EthereumError("Detector already registered")
        self.detectors[d.name] = d
        self.register_plugin(d)
        return d.name

    def unregister_detector(self, d):
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

    def generate_testcase(self, state, name, message=''):
        self._generate_testcase_callback(state, name, message)

    def current_location(self, state):
        world = state.platform
        address = world.current_vm.address
        pc = world.current_vm.pc
        at_init = world.current_transaction.sort == 'CREATE'
        output = io.StringIO()
        output.write('Contract: 0x{:x}\n'.format(address))
        output.write('EVM Program counter: 0x{:x}{:s}\n'.format(pc, at_init and " (at constructor)" or ""))
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
        # each object knows its secrets, each class should be able to report its
        # final state
        #super()._generate_testcase_callback(state, name, message)
        # TODO(mark): Refactor ManticoreOutput to let the platform be more in control
        #  so this function can be fully ported to EVMWorld.generate_workspace_files.
        blockchain = state.platform

        def flagged(flag):
            return '(*)' if flag else ''
        testcase = self._output.testcase(name.replace(' ', '_'))

        # call on_finalize for each plugin
        for plugin in self.plugins:
            on_finalize = getattr(plugin, 'on_finalize', None)
            if on_finalize:
                on_finalize(state, testcase)

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
                    findings.write('  Contract: 0x%x\n' % address)
                    findings.write('  EVM Program counter: 0x%x%s\n' % (pc, at_init and " (at constructor)" or ""))
                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc, runtime=not at_init)
                        findings.write('  Snippet:\n')
                        findings.write(src.replace('\n', '\n    ').strip())
                        findings.write('\n')

        with testcase.open_stream('summary') as summary:
            summary.write("Message: %s\n" % message)
            summary.write("Last exception: %s\n" % state.context.get('last_exception', 'None'))

            if last_tx:
                at_runtime = last_tx.sort != 'CREATE'
                address, offset, at_init = state.context['evm.trace'][-1]
                assert at_runtime != at_init

                #Last instruction if last tx vas valid
                if str(state.context['last_exception']) != 'TXERROR':
                    metadata = self.get_metadata(blockchain.last_transaction.address)
                    if metadata is not None:
                        summary.write('Last instruction at contract %x offset %x\n' % (address, offset))
                        source_code_snippet = metadata.get_source_for(offset, at_runtime)
                        if source_code_snippet:
                            summary.write('    '.join(source_code_snippet.splitlines(True)))
                        summary.write('\n')

            # Accounts summary
            is_something_symbolic = False
            summary.write("%d accounts.\n" % len(blockchain.accounts))
            for account_address in blockchain.accounts:
                is_account_address_symbolic = issymbolic(account_address)
                account_address = state.solve_one(account_address)

                summary.write("* %s::\n" % self.account_name(account_address))
                summary.write("Address: 0x%x %s\n" % (account_address, flagged(is_account_address_symbolic)))
                balance = blockchain.get_balance(account_address)
                is_balance_symbolic = issymbolic(balance)
                is_something_symbolic = is_something_symbolic or is_balance_symbolic
                balance = state.solve_one(balance)
                summary.write("Balance: %d %s\n" % (balance, flagged(is_balance_symbolic)))
                from .core.smtlib.visitors import translate_to_smtlib

                storage = blockchain.get_storage(account_address)
                summary.write("Storage: %s\n" % translate_to_smtlib(storage, use_bindings=True))

                all_used_indexes = []
                with state.constraints as temp_cs:
                    index = temp_cs.new_bitvec(256)
                    storage = blockchain.get_storage(account_address)
                    temp_cs.add(storage.get(index) != 0)

                    try:
                        while True:
                            a_index = solver.get_value(temp_cs, index)
                            all_used_indexes.append(a_index)

                            temp_cs.add(storage.get(a_index) != 0)
                            temp_cs.add(index != a_index)
                    except:
                        pass

                if all_used_indexes:
                    summary.write("Storage:\n")
                    for i in all_used_indexes:
                        value = storage.get(i)
                        is_storage_symbolic = issymbolic(value)
                        summary.write("storage[%x] = %x %s\n" % (state.solve_one(i), state.solve_one(value), flagged(is_storage_symbolic)))
                """if blockchain.has_storage(account_address):
                    summary.write("Storage:\n")
                    for offset, value in blockchain.get_storage_items(account_address):
                        is_storage_symbolic = issymbolic(offset) or issymbolic(value)
                        offset = state.solve_one(offset)
                        value = state.solve_one(value)
                        summary.write("\t%032x -> %032x %s\n" % (offset, value, flagged(is_storage_symbolic)))
                        is_something_symbolic = is_something_symbolic or is_storage_symbolic
                """

                runtime_code = state.solve_one(blockchain.get_code(account_address))
                if runtime_code:
                    summary.write("Code:\n")
                    fcode = io.BytesIO(runtime_code)
                    for chunk in iter(lambda: fcode.read(32), b''):
                        summary.write('\t%s\n' % binascii.hexlify(chunk))
                    runtime_trace = set((pc for contract, pc, at_init in state.context['evm.trace'] if address == contract and not at_init))
                    summary.write("Coverage %d%% (on this state)\n" % calculate_coverage(runtime_code, runtime_trace))  # coverage % for address in this account/state
                summary.write("\n")

            with self.locked_context('ethereum') as context:
                known_sha3 = context.get('_known_sha3', None)
                if known_sha3:
                    summary.write("Known hashes:\n")
                    for key, value in known_sha3:
                        summary.write('%s::%x\n' % (binascii.hexlify(key), value))

            if is_something_symbolic:
                summary.write('\n\n(*) Example solution given. Value is symbolic and may take other values\n')

        # Transactions
        with testcase.open_stream('tx') as tx_summary:
            is_something_symbolic = False
            for tx in blockchain.human_transactions:  # external transactions
                tx_summary.write("Transactions Nr. %d\n" % blockchain.transactions.index(tx))

                # The result if any RETURN or REVERT
                tx_summary.write("Type: %s (%d)\n" % (tx.sort, tx.depth))
                caller_solution = state.solve_one(tx.caller)
                caller_name = self.account_name(caller_solution)
                tx_summary.write("From: %s(0x%x) %s\n" % (caller_name, caller_solution, flagged(issymbolic(tx.caller))))
                address_solution = state.solve_one(tx.address)
                address_name = self.account_name(address_solution)
                tx_summary.write("To: %s(0x%x) %s\n" % (address_name, address_solution, flagged(issymbolic(tx.address))))
                tx_summary.write("Value: %d %s\n" % (state.solve_one(tx.value), flagged(issymbolic(tx.value))))
                tx_summary.write("Gas used: %d %s\n" % (state.solve_one(tx.gas), flagged(issymbolic(tx.gas))))
                tx_data = state.solve_one(tx.data)
                tx_summary.write("Data: %s %s\n" % (binascii.hexlify(tx_data), flagged(issymbolic(tx.data))))
                if tx.return_data is not None:
                    return_data = state.solve_one(tx.return_data)
                    tx_summary.write("Return_data: %s %s\n" % (binascii.hexlify(return_data), flagged(issymbolic(tx.return_data))))
                metadata = self.get_metadata(tx.address)
                if tx.sort == 'CREATE':
                    if metadata is not None:
                        args_data = tx.data[len(metadata._init_bytecode):]
                        arguments = ABI.deserialize(metadata.get_constructor_arguments(), state.solve_one(args_data))
                        is_argument_symbolic = any(map(issymbolic, arguments))
                        tx_summary.write('Function call:\n')
                        tx_summary.write("Constructor(")
                        tx_summary.write(','.join(map(repr, map(state.solve_one, arguments))))
                        tx_summary.write(') -> %s %s\n' % (tx.result, flagged(is_argument_symbolic)))

                if tx.sort == 'CALL':
                    if metadata is not None:
                        calldata = state.solve_one(tx.data)
                        is_calldata_symbolic = issymbolic(tx.data)

                        function_id = calldata[:4]  # hope there is enough data
                        signature = metadata.get_func_signature(function_id)
                        function_name = metadata.get_func_name(function_id)
                        if signature:
                            _, arguments = ABI.deserialize(signature, calldata)
                        else:
                            arguments = (calldata,)

                        return_data = None
                        if tx.result == 'RETURN':
                            ret_types = metadata.get_func_return_types(function_id)
                            return_data = state.solve_one(tx.return_data)
                            return_values = ABI.deserialize(ret_types, return_data)  # function return
                            is_return_symbolic = issymbolic(tx.return_data)

                        tx_summary.write('\n')
                        tx_summary.write("Function call:\n")
                        tx_summary.write("%s(" % function_name)
                        tx_summary.write(','.join(map(repr, arguments)))
                        tx_summary.write(') -> %s %s\n' % (tx.result, flagged(is_calldata_symbolic)))

                        if return_data is not None:
                            if len(return_values) == 1:
                                return_values = return_values[0]

                            tx_summary.write('return: %r %s\n' % (return_values, flagged(is_return_symbolic)))
                        is_something_symbolic = is_calldata_symbolic or is_return_symbolic

                tx_summary.write('\n\n')

            if is_something_symbolic:
                tx_summary.write('\n\n(*) Example solution given. Value is symbolic and may take other values\n')

        # logs
        with testcase.open_stream('logs') as logs_summary:
            is_something_symbolic = False
            for log_item in blockchain.logs:
                is_log_symbolic = issymbolic(log_item.memlog)
                is_something_symbolic = is_log_symbolic or is_something_symbolic
                solved_memlog = state.solve_one(log_item.memlog)
                printable_bytes = ''.join([c for c in map(chr, solved_memlog) if c in string.printable])

                logs_summary.write("Address: %x\n" % log_item.address)
                logs_summary.write("Memlog: %s (%s) %s\n" % (binascii.hexlify(solved_memlog), printable_bytes, flagged(is_log_symbolic)))
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

        #global summary
        if len(self.global_findings):
            with self._output.save_stream('global.findings') as global_findings:
                for address, pc, finding, at_init in self.global_findings:
                    global_findings.write('- %s -\n' % finding)
                    global_findings.write('  Contract: %s\n' % address)
                    global_findings.write('  EVM Program counter: 0x%x%s\n' % (pc, at_init and " (at constructor)" or ""))

                    md = self.get_metadata(address)
                    if md is not None:
                        source_code_snippet = md.get_source_for(pc, runtime=not at_init)
                        global_findings.write('  Solidity snippet:\n')
                        global_findings.write('    '.join(source_code_snippet.splitlines(True)))
                        global_findings.write('\n')

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

        logger.info("Results in %s", self.workspace)

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
