import hashlib
import binascii
import string
import re
import os
from . import Manticore
from .manticore import ManticoreError
from .core.smtlib import ConstraintSet, Operators, solver, issymbolic, istainted, taint_with, get_taints, Array, Expression, Constant, operators
from .core.smtlib.visitors import simplify
from .platforms import evm
from .core.state import State
import tempfile
from subprocess import Popen, PIPE, check_output
from multiprocessing import Process, Queue
from Queue import Empty as EmptyQueue
import sha3
import json
import logging
import StringIO
import cPickle as pickle
from .core.plugin import Plugin
from functools import reduce
from contextlib import contextmanager
logger = logging.getLogger(__name__)


class EthereumError(ManticoreError):
    pass


class DependencyError(EthereumError):
    def __init__(self, lib_names):
        super(DependencyError, self).__init__("You must pre-load and provide libraries addresses{ libname:address, ...} for %r" % lib_names)
        self.lib_names = lib_names


class DependencyError(EthereumError):
    def __init__(self, lib_names):
        super(DependencyError, self).__init__("You must pre-load and provide libraries addresses{ libname:address, ...} for %r" % lib_names)
        self.lib_names = lib_names


class NoAliveStates(EthereumError):
    pass


################ Detectors ####################
class Detector(Plugin):
    @property
    def name(self):
        return self.__class__.__name__.split('.')[-1]

    def get_findings(self, state):
        return state.context.setdefault('%s.findings' % self.name, set())

    @contextmanager
    def locked_global_findings(self):
        with self.manticore.locked_context('%s.global_findings' % self.name, set) as global_findings:
            yield global_findings

    @property
    def global_findings(self):
        with self.locked_global_findings() as global_findings:
            return global_findings

    def add_finding(self, state, address, pc, finding, init):
        self.get_findings(state).add((address, pc, finding, init))
        with self.locked_global_findings() as gf:
            gf.add((address, pc, finding, init))
        #Fixme for ever broken logger 
        #logger.warning(finding)

    def add_finding_here(self, state, finding):
        address = state.platform.current_vm.address
        pc = state.platform.current_vm.pc
        at_init = state.platform.current_transaction.sort == 'CREATE'
        self.add_finding(state, address, pc, finding, at_init)

    def _save_current_location(self, state, finding):
        address = state.platform.current_vm.address
        pc = state.platform.current_vm.pc
        location = (address, pc, finding)
        hash_id = hashlib.sha1(str(location)).hexdigest()
        state.context.setdefault('%s.locations' % self.name, {})[hash_id] = location
        return hash_id

    def _get_location(self, state, hash_id):
        return state.context.setdefault('%s.locations' % self.name, {})[hash_id]

    def _get_src(self, address, pc):
        return self.manticore.get_metadata(address).get_source_for(pc)

    def report(self, state):
        output = ''
        for address, pc, finding in self.get_findings(state):
            output += 'Finding %s\n' % finding
            output += '\t Contract: %s\n' % address
            output += '\t Program counter: %s\n' % pc
            output += '\t Snippet:\n'
            output += '\n'.join(('\t ' + x for x in self._get_src(address, pc).split('\n')))
            output += '\n'
        return output


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
        super(FilterFunctions, self).__init__(**kwargs)
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
                constraint = reduce(Operators.OR, map(lambda x: tx.data[:4] == x.decode('hex'), selected_functions))
                state.constrain(constraint)
            else:
                #Avoid all not seleted hashes
                for func_hsh in md.hashes:
                    if func_hsh in selected_functions:
                        constraint = Operators.NOT(tx.data[:4] == func_hsh.decode('hex'))
                        state.constrain(constraint)


class DetectInvalid(Detector):
    def __init__(self, only_human=True, **kwargs):
        """
        Detects INVALID instructions.

        INVALID instructions are originally designated to signal exceptional code.
        As in practice the INVALID instruction is used in different ways this 
        detector may Generate a great deal of false positives.

        :param only_human: if True report only INVALID at depth 0 transactions
        """
        super(DetectInvalid, self).__init__(**kwargs)
        self._only_human = only_human

    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result_ref):
        mnemonic = instruction.semantics
        result = result_ref.value

        if mnemonic == 'INVALID':
            if not self._only_human or state.platform.current_transaction.depth == 0:
                self.add_finding_here(state, "INVALID intruction")


class DetectIntegerOverflow(Detector):
    '''
        Detects potential overflow and underflow conditions on ADD and SUB instructions.
    '''
    @staticmethod
    def _can_add_overflow(state, result, a, b):
        # TODO FIXME (mark) this is using a signed LT. need to check if this is correct
        return state.can_be_true(operators.ULT(result, a) | operators.ULT(result, b))

    @staticmethod
    def _can_mul_overflow(state, result, a, b):
        return state.can_be_true(operators.ULT(result, a) & operators.ULT(result, b))

    @staticmethod
    def _can_sub_underflow(state, a, b):
        return state.can_be_true(b > a)

    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result_ref):
        result = result_ref.value
        mnemonic = instruction.semantics

        if mnemonic == 'ADD':
            if self._can_add_overflow(state, result, *arguments):
                self.add_finding_here(state, "Integer overflow at {} instruction".format(mnemonic))
                if issymbolic(result):
                    result._taint = result.taint | frozenset(("IOA",))
        elif mnemonic == 'MUL':
            if self._can_mul_overflow(state, result, *arguments):
                self.add_finding_here(state, "Integer overflow at {} instruction".format(mnemonic))
                if issymbolic(result):
                    result._taint = result.taint | frozenset(("IOM",))
        elif mnemonic == 'SUB':
            if self._can_sub_underflow(state, *arguments):
                self.add_finding_here(state, "Integer underflow at {} instruction".format(mnemonic))
                if issymbolic(result):
                    result._taint = result.taint | frozenset(("IU",))
        if mnemonic == 'SSTORE':
            for arg in arguments:
                if istainted(arg, 'IOA') or istainted(arg, 'IOM') or istainted(arg, 'IU'):
                    self.add_finding_here(state, "Result of integer overflowed intruction is written to the storage")
        result_ref.value = result


class DetectIntegerOverflow(Detector):
    '''
        Detects potential overflow and underflow conditions on ADD and SUB instructions.
    '''

    def _save_current_location(self, state, finding, condition):
        address = state.platform.current_vm.address
        pc = state.platform.current_vm.pc
        at_init = state.platform.current_transaction.sort == 'CREATE'
        location = (address, pc, finding, at_init, condition)
        hash_id = hashlib.sha1(str(location)).hexdigest()
        state.context.setdefault('%s.locations' % self.name, {})[hash_id] = location
        return hash_id

    def _get_location(self, state, hash_id):
        return state.context.setdefault('%s.locations' % self.name, {})[hash_id]

    @staticmethod
    def _can_signed_sub_overflow(state, a, b):
        '''
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
        '''
        sub = Operators.SEXTEND(a, 256, 512) - Operators.SEXTEND(b, 256, 512)
        cond = Operators.OR(sub < -(1 << 256), sub >= (1 << 255))
        return cond

    @staticmethod
    def _can_signed_add_overflow(state, a, b):
        '''
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
        '''
        add = Operators.SEXTEND(a, 256, 512) + Operators.SEXTEND(b, 256, 512)
        cond = Operators.OR(add < -(1 << 256), add >= (1 << 255))
        return cond

    @staticmethod
    def _can_unsigned_sub_overflow(state, a, b):
        '''
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
        '''
        cond = Operators.UGT(b, a)
        return cond

    @staticmethod
    def _can_unsigned_add_overflow(state, a, b):
        '''
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
        '''
        add = Operators.ZEXTEND(a, 512) + Operators.ZEXTEND(b, 512)
        cond = Operators.UGE(add, 1 << 256)
        return cond

    @staticmethod
    def _can_signed_mul_overflow(state, a, b):
        '''
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

        '''
        mul = Operators.SEXTEND(a, 256, 512) * Operators.SEXTEND(b, 256, 512)
        cond = Operators.OR(mul < -(1 << 255), mul >= (1 << 255))
        return cond

    @staticmethod
    def _can_unsigned_mul_overflow(state, a, b):
        '''
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

        '''
        mul = Operators.SEXTEND(a, 256, 512) * Operators.SEXTEND(b, 256, 512)
        cond = Operators.UGE(mul, 1<<256)
        return cond

    def did_evm_execute_instruction_callback(self, state, instruction, arguments, result_ref):
        mnemonic = instruction.semantics
        result = result_ref.value
        ios = False
        iou = False

        if mnemonic == 'ADD':
            ios = self._can_signed_add_overflow(state, *arguments)
            iou = self._can_unsigned_add_overflow(state, *arguments)
        elif mnemonic == 'MUL':
            ios = self._can_signed_mul_overflow(state, *arguments)
            iou = self._can_unsigned_mul_overflow(state, *arguments)
        elif mnemonic == 'SUB':
            ios = self._can_signed_sub_overflow(state, *arguments)
            iou = self._can_unsigned_sub_overflow(state, *arguments)
        elif mnemonic == 'SSTORE':
            where, what = arguments
            if istainted(what, "SIGNED"):
                for taint in get_taints(what, "IOS_.*"):
                    loc = self._get_location(state, taint[4:])
                    if state.can_be_true(loc[-1]):
                        self.add_finding(state, *loc[:-1])
            else:
                for taint in get_taints(what, "IOU_.*"):
                    loc = self._get_location(state, taint[4:]) 
                    if state.can_be_true(loc[-1]):
                        self.add_finding(state, *loc[:-1])

        if mnemonic in ('SLT', 'SGT', 'SDIV', 'SMOD'):
            result = taint_with(result, "SIGNED" % id_val)

        if state.can_be_true(ios):
            id_val = self._save_current_location(state, "Signed integer overflow at %s instruction" % mnemonic, ios)
            result = taint_with(result, "IOS_%s" % id_val)
        if state.can_be_true(iou):
            id_val = self._save_current_location(state, "Unsigned integer overflow at %s instruction" % mnemonic, iou)
            result = taint_with(result, "IOU_%s" % id_val)
        #if ios and iou:
        #    self.add_finding_here(state, "Integer overflow at %s" % mnemonic)

        result_ref.value = result


class DetectUninitializedMemory(Detector):
    '''
        Detects uses of uninitialized memory
    '''

    def did_evm_read_memory_callback(self, state, offset, value):
        initialized_memory = state.context.get('seth.detectors.initialized_memory', set())
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
        state.context.setdefault('seth.detectors.initialized_memory', set()).add((current_contract, offset))


class DetectUninitializedStorage(Detector):
    '''
        Detects uses of uninitialized storage
    '''

    def did_evm_read_storage_callback(self, state, address, offset, value):
        if not state.can_be_true(value != 0):
            # Not initialized memory should be zero
            return
        # check if offset is known
        cbu = True  # Can be unknown
        for known_address, known_offset in state.context['seth.detectors.initialized_storage']:
            cbu = Operators.AND(cbu, Operators.OR(address != known_address, offset != known_offset))

        if state.can_be_true(cbu):
            self.add_finding_here(state, "Potentially reading uninitialized storage")

    def did_evm_write_storage_callback(self, state, address, offset, value):
        # concrete or symbolic write
        state.context.setdefault('seth.detectors.initialized_storage', set()).add((address, offset))


def calculate_coverage(runtime_bytecode, seen):
    ''' Calculates what percentage of runtime_bytecode has been seen '''
    count, total = 0, 0
    bytecode = SolidityMetadata._without_metadata(runtime_bytecode)
    for i in evm.EVMAsm.disassemble_all(bytecode):
        if i.offset in seen:
            count += 1
        total += 1

    if total == 0:
        #No runtime_bytecode
        return 0
    return count * 100.0 / total


class SolidityMetadata(object):
    def __init__(self, name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings):
        ''' Contract metadata for Solidity-based contracts '''
        self.name = name
        self.source_code = source_code
        self._init_bytecode = init_bytecode
        self._runtime_bytecode = runtime_bytecode
        self._hashes = hashes
        self.abi = dict([(item.get('name', '{fallback}'), item) for item in abi])
        self.warnings = warnings
        self.srcmap_runtime = self.__build_source_map(self.runtime_bytecode, srcmap_runtime)
        self.srcmap = self.__build_source_map(self.init_bytecode, srcmap)

    def add_function(self, method_name_and_signature):
        #TODO: use re, and check it's sane
        if name in self.abi:
            raise Exception("Function already defined")
        hsh = ABI.make_function_id(method_name_and_signature)
        name = method_name_and_signature.split('(')[0]
        self._hashes.append(method_name_and_signature, hsh)

        input_types = method_name_and_signature.split('(')[1].split(')')[0].split(',')
        output_types = method_name_and_signature.split(')')[1].split(',')
        self.abi[name] = {'inputs': [{'type': ty} for ty in input_types],
                          'name': name,
                          'outputs': [{'type': ty} for ty in output_types]}

    @staticmethod
    def _without_metadata(bytecode):
        end = None
        if bytecode[-43: -34] == '\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
                and bytecode[-2:] == '\x00\x29':
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
        for i in evm.EVMAsm.disassemble_all(bytecode):
            pos_to_offset[asm_pos] = asm_offset
            asm_pos += 1
            asm_offset += i.size

        for asm_pos, md in enumerate(srcmap):
            if len(md):
                d = dict((p, k) for p, k in enumerate(md.split(':')) if k)

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
        ''' Solidity source code snippet related to `asm_pos` evm bytecode offset.
            If runtime is False, initialization bytecode source map is used
        '''
        if runtime:
            srcmap = self.srcmap_runtime
        else:
            srcmap = self.srcmap

        try:
            #print asm_offset, srcmap[asm_offset]
            beg, size, _, _ = srcmap[asm_offset]
        except KeyError:
            #asm_offset pointing outside the known bytecode
            return ''

        output = ''
        nl = self.source_code.count('\n')
        snippet = self.source_code[beg:beg + size]
        for l in snippet.split('\n'):
            output += '    %s  %s\n' % (nl, l)
            nl += 1
        return output

    @property
    def signatures(self):
        return dict(((b, a) for (a, b) in self._hashes.items()))

    def get_abi(self, hsh):
        func_name = self.get_func_name(hsh)
        default_fallback_abi = {u'stateMutability': u'nonpayable', u'payable': False, u'type': u'fallback'}
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
        return self.signatures.get(hsh, '{fallback}()')

    def get_hash(self, method_name_and_signature):
        #helper
        return ABI.make_function_id(method_name_and_signature)

    @property
    def functions(self):
        return tuple(self.signatures.values()) + ('{fallback}()',)

    @property
    def hashes(self):
        return tuple(self.signatures.keys()) + ('00000000',)


class ABI(object):
    '''
        This class contains methods to handle the ABI.
        The Application Binary Interface is the standard way to interact with
        contracts in the Ethereum ecosystem, both from outside the blockchain
        and for contract-to-contract interaction.

    '''
    class SByte():
        ''' Unconstrained symbolic byte string, not associated with any ConstraintSet '''

        def __init__(self, size=1):
            self.size = size

        def __mul__(self, reps):
            return Symbol(self.size * reps)

    SCHAR = SByte(1)
    SUINT = SByte(32)
    SValue = None

    @staticmethod
    def serialize(value):
        '''
        Translates a Python object to its EVM ABI serialization.
        '''
        if isinstance(value, (str, tuple)):
            return ABI.serialize_string(value)
        if isinstance(value, (list)):
            return ABI.serialize_array(value)
        if isinstance(value, (int, long)):
            return ABI.serialize_uint(value)
        if isinstance(value, ABI.SByte):
            return ABI.serialize_uint(value.size) + (None,) * value.size + (('\x00',) * (32 - (value.size % 32)))
        if value is None:
            return (None,) * 32

    @staticmethod
    def serialize_uint(value, size=32):
        '''
        Translates a Python int into a 32 byte string, MSB first
        '''
        assert size >= 1
        bytes = []
        for position in range(size):
            bytes.append(Operators.EXTRACT(value, position * 8, 8))
        chars = map(Operators.CHR, bytes)
        return tuple(reversed(chars))

    @staticmethod
    def serialize_string(value):
        '''
        Translates a string or a tuple of chars its EVM ABI serialization
        '''
        assert isinstance(value, (str, tuple))
        return ABI.serialize_uint(len(value)) + tuple(value) + tuple('\x00' * (32 - (len(value) % 32)))

    @staticmethod
    def serialize_array(value):
        assert isinstance(value, list)
        serialized = [ABI.serialize_uint(len(value))]
        for item in value:
            # TODO check all values are the same type
            serialized.append(ABI.serialize(item))
        return reduce(lambda x, y: x + y, serialized)

    @staticmethod
    def make_function_id(method_name_and_signature):
        '''
        Makes a function hash id from a method signature
        '''
        s = sha3.keccak_256()
        s.update(method_name_and_signature)
        return s.hexdigest()[:8].decode('hex')

    @staticmethod
    def make_function_arguments(*args):
        ''' Serializes a sequence of arguments '''
        if len(args) == 0:
            return ()
        args = list(args)
        for i in range(len(args)):
            if isinstance(args[i], EVMAccount):
                args[i] = int(args[i])
        result = []
        dynamic_args = []
        dynamic_offset = 32 * len(args)
        for arg in args:
            if isinstance(arg, (list, tuple, str, ManticoreEVM.SByte)):
                result.append(ABI.serialize(dynamic_offset))
                serialized_arg = ABI.serialize(arg)
                dynamic_args.append(serialized_arg)
                assert len(serialized_arg) % 32 == 0
                dynamic_offset += len(serialized_arg)
            else:
                result.append(ABI.serialize(arg))

        for arg in dynamic_args:
            result.append(arg)

        return reduce(lambda x, y: x + y, result)

    @staticmethod
    def make_function_call(method_name, *args):
        function_id = ABI.make_function_id(method_name)
        assert len(function_id) == 4
        result = [tuple(function_id)]
        result.append(ABI.make_function_arguments(*args))
        return reduce(lambda x, y: x + y, result)

    @staticmethod
    def _parse_size(num):
        """
        Parses the size part of a uint or int Solidity declaration.
        If empty string, returns 256

        :param str num: text following uint/int in a Solidity type declaration
        :return: uint or int size
        :rtype: int
        :raises EthereumError: if invalid size
        """
        if not num:
            return 256

        malformed = False
        try:
            size = int(num)
        except ValueError:
            malformed = True

        if malformed or size < 8 or size > 256 or size % 8 != 0:
            raise EthereumError('Invalid type size: {}'.format(num))

        return size

    @staticmethod
    def get_uint(data, nbytes, offset):
        """
        Read a `nbytes` bytes long big endian unsigned integer from `data` starting at `offset` 

        :param data: sliceable buffer; symbolic buffer of Eth ABI encoded data
        :param offset: byte offset
        :param nbytes: number of bytes to read starting from least significant byte
        :rtype: int or Expression
        """
        def _simplify(x):
            value = simplify(x)
            if isinstance(value, Constant) and not value.taint:
                return value.value
            else:
                return value
        nbytes = _simplify(nbytes)
        offset = _simplify(offset)
        padding = 32 - nbytes
        start = offset + padding
        values = []
        pos = start
        while pos < start + nbytes:
            if pos > len(data):
                values.append('\x00')
            else:
                values.append(data[pos])
            pos = pos + 1
        #value = Operators.CONCAT(nbytes * 8, *[Operators.ORD(x) for x in data[start:start + nbytes]])
        value = Operators.CONCAT(nbytes * 8, *[Operators.ORD(x) for x in values])
        return _simplify(value)

    @staticmethod
    def _consume_type(ty, data, offset):
        """
        Parses a value of type from data

        Further info: http://solidity.readthedocs.io/en/develop/abi-spec.html#use-of-dynamic-types

        :param data: transaction data WITHOUT the function hash first 4 bytes
        :param offset: offset into data of the first byte of the "head part" of the ABI element
        :return: tuple where the first element is the extracted ABI element, and the second is the offset of
            the next ABI element
        :rtype: tuple
        """
        # TODO(mark) refactor so we don't return this tuple thing. the offset+32 thing
        # should be something the caller keeps track of.

        new_offset = offset + 32

        if ty == u'':
            new_offset = offset
            result = None
        elif ty.startswith('uint'):
            size = ABI._parse_size(ty[4:]) // 8
            result = ABI.get_uint(data, size, offset)
        elif ty.startswith('int'):
            size = ABI._parse_size(ty[3:])
            value = ABI.get_uint(data, size // 8, offset)
            mask = 2**(size - 1)
            value = -(value & mask) + (value & ~mask)
            result = value
        elif ty == u'bool':
            result = ABI.get_uint(data, 1, offset)
        elif ty == u'address':
            result = ABI.get_uint(data, 20, offset)
        elif ty in (u'bytes', u'string'):
            dyn_offset = ABI.get_uint(data, 32, offset)
            size = ABI.get_uint(data, 32, dyn_offset)
            result = data[dyn_offset + 32:dyn_offset + 32 + size]
        elif ty.startswith('bytes') and 0 <= int(ty[5:]) <= 32:
            size = int(ty[5:])
            result = data[offset:offset + size]
        elif ty == u'function':
            # `function` is a special case of `bytes24`
            size = 24
            result = data[offset:offset + size]
        elif ty == u'address[]':
            dyn_offset = simplify(ABI.get_uint(data, 32, offset))
            size = simplify(ABI.get_uint(data, 32, dyn_offset))
            result = [ABI.get_uint(data, 20, dyn_offset + 32 + 32 * i) for i in range(size)]
        else:
            raise NotImplementedError(repr(ty))

        return result, new_offset

    @staticmethod
    def parse_type_spec(type_spec):
        is_multiple = '(' in type_spec
        if is_multiple:
            func_name = type_spec.split('(')[0]
            types = type_spec.split('(')[1][:-1].split(',')
            if not func_name:
                func_name = None
        else:
            func_name = None
            types = (type_spec,)
        return is_multiple, func_name, types

    @staticmethod
    def parse(type_spec, data):
        ''' Deserialize function ID and arguments specified in `type_spec` from `data`

        :param str type_spec: EVM ABI function specification. function name is optional
        :param data: ethereum transaction data
        :type data: str or Array
        :return:
        '''
        is_multiple, func_name, types = ABI.parse_type_spec(type_spec)

        off = 0

        #If it parsed the function name from the spec, skip 4 bytes from the data
        if func_name:
            data = data[4:]

        arguments = []
        for ty in types:
            val, off = ABI._consume_type(ty, data, off)
            if val is not None:
                arguments.append(val)
            else:
                break

        if is_multiple:
            if func_name is not None:
                return func_name, tuple(arguments)
            else:
                return tuple(arguments)
        else:
            return arguments[0]


class EVMAccount(object):
    ''' An EVM account '''

    def __init__(self, address, m=None, default_caller=None):
        ''' Encapsulates an account.

            :param address: the address of this account
            :type address: 160 bit long integer
            :param seth: the controlling Manticore
            :param default_caller: the default caller address for any transaction

        '''
        self._default_caller = default_caller
        self._m = m
        self._address = address
        self._hashes = None

    def add_function(self, signature):
        func_id = ABI.make_function_id(signature)
        func_name = str(signature.split('(')[0])
        self._hashes[func_name] = signature, func_id

    def __int__(self):
        return self._address

    def __str__(self):
        return str(self._address)

    @property
    def address(self):
        return self._address

    def _null_func(self):
        pass

    def _init_hashes(self):
        #initializes self._hashes lazy
        if self._hashes is None and self._m is not None:
            self._hashes = {}
            md = self._m.get_metadata(self._address)
            if md is not None:
                for signature, func_id in md._hashes.items():
                    func_name = str(signature.split('(')[0])
                    self._hashes[func_name] = signature, func_id
            # It was successful, no need to re-run. _init_hashes disabled
            self._init_hashes = self._null_func

    def __getattribute__(self, name):
        ''' If this is a contract account of which we know the functions hashes,
            this will build the transaction for the function call.

            Example use::

                #call funtion `add` on contract_account with argument `1000`
                contract_account.add(1000)

        '''
        if not name.startswith('_'):
            self._init_hashes()
            if self._hashes is not None and name in self._hashes.keys():
                def f(*args, **kwargs):
                    caller = kwargs.get('caller', None)
                    value = kwargs.get('value', 0)
                    tx_data = ABI.make_function_call(str(self._hashes[name][0]), *args)
                    if caller is not None:
                        caller = int(caller)
                    else:
                        caller = self._default_caller
                    self._m.transaction(caller=caller,
                                        address=self._address,
                                        value=value,
                                        data=tx_data)
                return f

        return object.__getattribute__(self, name)


class ManticoreEVM(Manticore):
    ''' Manticore EVM manager

        Usage Ex::

            from manticore.ethereum import ManticoreEVM, ABI
            m = ManticoreEVM()
            #And now make the contract account to analyze
            source_code = """
                pragma solidity ^0.4.15;
                contract AnInt {
                    uint private i=0;
                    function set(uint value){
                        i=value
                    }
                }
            """
            #Initialize user and contracts
            user_account = m.create_account(balance=1000)
            contract_account = m.solidity_create_contract(source_code, owner=user_account, balance=0)
            contract_account.set(12345, value=100) 

            seth.report()
            print seth.coverage(contract_account)
    '''
    SByte = ABI.SByte
    SValue = ABI.SValue

    def make_symbolic_buffer(self, size):
        ''' Creates a symbolic buffer of size bytes to be used in transactions.
            You can not operate on it. It is intended as a place holder for the
            real expression.

            Example use::

                symbolic_data = seth.make_symbolic_buffer(320)
                seth.transaction(caller=attacker_account,
                                address=contract_account,
                                data=symbolic_data,
                                value=100000 )


        '''
        return ABI.SByte(size)

    def make_symbolic_value(self):
        ''' Creates a symbolic value, normally a uint256, to be used in transactions.
            You can not operate on it. It is intended as a place holder for the
            real expression.

            Example use::

                symbolic_value = seth.make_symbolic_value()
                seth.transaction(caller=attacker_account,
                                address=contract_account,
                                data=data,
                                value=symbolic_data )

        '''
        return ABI.SValue

    @staticmethod
    def compile(source_code, contract_name=None, libraries=None, runtime=False):
        ''' Get initialization bytecode from a Solidity source code '''
        name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings = ManticoreEVM._compile(source_code, contract_name, libraries)
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
                    hex_contract_lst[pos:pos + 40] = '%040x' % lib_address
            hex_contract = ''.join(hex_contract_lst)
        return binascii.unhexlify(hex_contract)

    @staticmethod
    def _run_solc(source_file):
        ''' Compile a source file with the Solidity compiler

            :param source_file: a file object for the source file
            :return: output, warnings
        '''
        solc = "solc"

        #check solc version
        supported_versions = ('0.4.18', '0.4.21')

        try:
            installed_version_output = check_output([solc, "--version"])
        except OSError:
            raise Exception("Solidity compiler not installed.")

        m = re.match(r".*Version: (?P<version>(?P<major>\d+)\.(?P<minor>\d+)\.(?P<build>\d+))\+(?P<commit>[^\s]+).*", installed_version_output, re.DOTALL | re.IGNORECASE)

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
            '--combined-json', 'abi,srcmap,srcmap-runtime,bin,hashes,bin-runtime',
            '--allow-paths', '.',
            filename
        ]
        p = Popen(solc_invocation, stdout=PIPE, stderr=PIPE, cwd=working_folder)
        with p.stdout as stdout, p.stderr as stderr:
            try:
                return json.loads(stdout.read()), stderr.read()
            except ValueError:
                raise Exception('Solidity compilation error:\n\n{}'.format(stderr.read()))

    @staticmethod
    def _compile(source_code, contract_name, libraries=None):
        """ Compile a Solidity contract, used internally

            :param source_code: solidity source as either a string or a file handle
            :param contract_name: a string with the name of the contract to analyze
            :param libraries: an itemizable of pairs (library_name, address) 
            :return: name, source_code, bytecode, srcmap, srcmap_runtime, hashes
            :return: name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings
        """

        try:
            file_type = file  # Python 2
        except NameError:
            from io import IOBase
            file_type = IOBase  # Python 3

        if isinstance(source_code, str):
            with tempfile.NamedTemporaryFile() as temp:
                temp.write(source_code)
                temp.flush()
                output, warnings = ManticoreEVM._run_solc(temp)
        elif isinstance(source_code, file_type):
            output, warnings = ManticoreEVM._run_solc(source_code)
            source_code = source_code.read()
        else:
            raise TypeError

        contracts = output.get('contracts', [])
        if len(contracts) != 1 and contract_name is None:
            raise Exception('Solidity file must contain exactly one contract or you must use contract parameter to specify which one.')

        name, contract = None, None
        if contract_name is None:
            name, contract = contracts.items()[0]
        else:
            for n, c in contracts.items():
                if n.split(":")[1] == contract_name:
                    name, contract = n, c
                    break

        assert(name is not None)
        name = name.split(':')[1]

        if contract['bin'] == '':
            raise Exception('Solidity failed to compile your contract.')

        bytecode = ManticoreEVM._link(contract['bin'], libraries)
        srcmap = contract['srcmap'].split(';')
        srcmap_runtime = contract['srcmap-runtime'].split(';')
        hashes = contract['hashes']
        abi = json.loads(contract['abi'])
        runtime = ManticoreEVM._link(contract['bin-runtime'], libraries)
        return name, source_code, bytecode, runtime, srcmap, srcmap_runtime, hashes, abi, warnings

    def __init__(self, procs=10, **kwargs):
        ''' A Manticore EVM manager
            :param int procs: number of workers to use in the exploration
        '''
        self.normal_accounts = set()
        self.contract_accounts = set()
        self._config_procs = procs
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)
        initial_state = State(constraints, world)
        super(ManticoreEVM, self).__init__(initial_state, **kwargs)

        self.detectors = {}
        self.metadata = {}

        # The following should go to manticore.context so we can use multiprocessing
        self.context['seth'] = {}
        self.context['seth']['_pending_transaction'] = None
        self.context['seth']['_saved_states'] = []
        self.context['seth']['_final_states'] = []
        self.context['seth']['_completed_transactions'] = 0

        self._executor.subscribe('did_load_state', self._load_state_callback)
        self._executor.subscribe('will_terminate_state', self._terminate_state_callback)
        self._executor.subscribe('did_evm_execute_instruction', self._did_evm_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self._did_evm_read_code)
        self._executor.subscribe('on_symbolic_sha3', self._symbolic_sha3)
        self._executor.subscribe('on_concrete_sha3', self._concrete_sha3)

    @property
    def world(self):
        ''' The world instance or None if there is more than one state '''
        return self.get_world(None)

    @property
    def completed_transactions(self):
        with self.locked_context('seth') as context:
            return context['_completed_transactions']

    @property
    def _running_state_ids(self):
        ''' IDs of the running states'''
        with self.locked_context('seth') as context:
            if self.initial_state is not None:
                return context['_saved_states'] + [-1]
            else:
                return context['_saved_states']

    @property
    def _terminated_state_ids(self):
        ''' IDs of the terminated states '''
        with self.locked_context('seth') as context:
            return context['_final_states']

    @property
    def _all_state_ids(self):
        ''' IDs of the all states

            Note: state with id -1 is already in memory and it is not backed on the storage
        '''
        return self._running_state_ids + self._terminated_state_ids

    @property
    def running_states(self):
        ''' Iterates over the running states'''
        for state_id in self._running_state_ids:
            state = self.load(state_id)
            yield state
            #FIXME re save state in case it was modified by the user

    @property
    def terminated_states(self):
        ''' Iterates over the terminated states'''
        for state_id in self._terminated_state_ids:
            state = self.load(state_id)
            yield state
            #FIXME re save state in case it was modified by the user

    @property
    def all_states(self):
        ''' Iterates over the all states (terminated and alive)'''
        for state_id in self._all_state_ids:
            state = self.load(state_id)
            yield state
            #FIXME re save state in case it was modified by the user

    def count_states(self):
        ''' Total states count '''
        return len(self._all_state_ids)

    def count_running_states(self):
        ''' Running states count '''
        return len(self._running_state_ids)

    def count_terminated_states(self):
        ''' Terminated states count '''
        return len(self._terminated_state_ids)

    def _terminate_state_id(self, state_id):
        ''' Manually terminates a states by state_id.
            Moves the state from the running list into the terminated list
        '''

        # Move state from running to final
        if state_id != -1:
            with self.locked_context('seth') as seth_context:
                saved_states = seth_context['_saved_states']
                final_states = seth_context['_final_states']
                if state_id in saved_states:
                    saved_states.remove(state_id)
                    final_states.append(state_id)
                seth_context['_saved_states'] = saved_states
                seth_context['_final_states'] = final_states
        else:
            assert state_id == -1
            state_id = self.save(self._initial_state, final=True)
            self._initial_state = None
        return state_id

    def _revive_state_id(self, state_id):
        ''' Manually revice a states by state_id.
            Moves the state from the final list into the running list
        '''

        # Move state from final to running
        if state_id != -1:
            with self.locked_context('seth') as seth_context:
                saved_states = seth_context['_saved_states']
                final_states = seth_context['_final_states']
                if state_id in final_states:
                    final_states.remove(state_id)
                    saved_states.append(state_id)
                seth_context['_saved_states'] = saved_states
                seth_context['_final_states'] = final_states
        return state_id

    # deprecate this 5 in favor of for sta in seth.all_states: do stuff?

    def get_world(self, state_id=None):
        ''' Returns the evm world of `state_id` state. '''
        state = self.load(state_id)
        if state is None:
            return None
        else:
            return state.platform

    def get_balance(self, address, state_id=None):
        ''' Balance for account `address` on state `state_id` '''
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_balance(address)

    def get_storage_data(self, address, offset, state_id=None):
        ''' Storage data for `offset` on account `address` on state `state_id` '''
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_storage_data(address, offset)

    def get_code(self, address, state_id=None):
        ''' Storage data for `offset` on account `address` on state `state_id` '''
        if isinstance(address, EVMAccount):
            address = int(address)
        return self.get_world(state_id).get_code(address)

    def last_return(self, state_id=None):
        ''' Last returned buffer for state `state_id` '''
        state = self.load(state_id)
        return state.platform.last_return_data

    def transactions(self, state_id=None):
        ''' Transactions list for state `state_id` '''
        state = self.load(state_id)
        return state.platform.transactions

    def solidity_create_contract(self, source_code, owner, contract_name=None, libraries=None, balance=0, address=None, args=()):
        ''' Creates a solidity contract and library dependencies

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
            :rtype: EVMAccount
        '''
        if libraries is None:
            deps = {}
        else:
            deps = dict(libraries)
        # If not selected get a new one for the main contract
        if address is None:
            address = self.world.new_address()

        contract_names = [contract_name]
        while contract_names:
            contract_name_i = contract_names.pop()
            try:
                compile_results = self._compile(source_code, contract_name_i, libraries=deps)
                init_bytecode = compile_results[2]

                if contract_name_i == contract_name:
                    contract_account = self.create_contract(owner=owner,
                                                            balance=balance,
                                                            address=address,
                                                            init=tuple(init_bytecode) + tuple(ABI.make_function_arguments(*args)))
                else:
                    contract_account = self.create_contract(owner=owner, init=tuple(init_bytecode))

                if contract_account is None:
                    raise Exception("Failed to build contract %s" % contract_name_i)
                self.metadata[int(contract_account)] = SolidityMetadata(*compile_results)

                deps[contract_name_i] = contract_account
            except DependencyError as e:
                contract_names.append(contract_name_i)
                for lib_name in e.lib_names:
                    if lib_name not in deps:
                        contract_names.append(lib_name)

        if not self.count_running_states() or self.get_code(contract_account) == '':
            return None
        return contract_account

    def create_contract(self, owner, balance=0, address=None, init=None):
        ''' Creates a contract

            :param owner: owner account (will be default caller in any transactions)
            :type owner: int or EVMAccount
            :param balance: balance to be transferred on creation
            :type balance: int or SValue
            :param int address: the address for the new contract (optional)
            :param str init: initializing evm bytecode and arguments
            :rtype: EVMAccount
        '''
        assert self.count_running_states() == 1, "No forking yet"
        assert init is not None
        #FIxme?
        #We force the same address/accounts on all the states
        if address is None:
            address = self.world.new_address()

        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is None
            context['_pending_transaction'] = ('CREATE_CONTRACT', owner, address, balance, init, 10)

        self.run(procs=self._config_procs)

        #FIxme?
        #We assume the constructor run in all states effectivelly and add the
        #address to the accounts list
        self.contract_accounts.add(address)
        return EVMAccount(address, self, default_caller=owner)

    def create_account(self, balance=0, address=None, code=''):
        ''' Creates a normal account

            :param balance: balance to be transfered on creation
            :type balance: int or SValue
            :param address: the address for the new contract (optional)
            :type address: int
            :return: an EVMAccount
        '''
        if self.count_running_states() != 1:
            raise Exception("This works only when there is a single state")
        with self.locked_context('seth') as context:
            if context['_pending_transaction'] is not None:
                raise Exception("It should be no other pending transaction")

        #self.world refers to the evm world of the single state in existance
        address = self.world.new_address()
        self.world.create_account(address, balance, code=code, storage=None)

        #keep a list just in case.
        #Caveat: After some execution the account list on different states may differ
        self.normal_accounts.add(address)
        return address

    def transaction(self, caller, address, value, data):
        ''' Issue a symbolic transaction in all running states

            :param caller: the address of the account sending the transaction
            :type caller: int or EVMAccount
            :param address: the address of the contract to call
            :type address: int or EVMAccount
            :param value: balance to be transfered on creation
            :type value: int or SValue
            :param data: initial data
            :return: an EVMAccount
            :raises NoAliveStates: if there are no alive states to execute
        '''
        if isinstance(address, EVMAccount):
            address = int(address)
        if isinstance(caller, EVMAccount):
            caller = int(caller)

        if not self.count_running_states():
            raise NoAliveStates

        #Fixme
        if isinstance(data, self.SByte):
            data = (None,) * data.size

        with self.locked_context('seth') as context:
            context['_pending_transaction'] = ('CALL', caller, address, value, data, 10)

        logger.info("Starting symbolic transaction: %d", self.completed_transactions + 1)
        status = self.run(procs=self._config_procs)
        with self.locked_context('seth') as context:
            context['_completed_transactions'] = context['_completed_transactions'] + 1

        logger.info("Finished symbolic transaction: %d | Code Coverage: %d%% | Terminated States: %d | Alive States: %d", self.completed_transactions, self.global_coverage(address), self.count_terminated_states(), self.count_running_states())

        return status

    def multi_tx_analysis(self, solidity_filename, contract_name=None, tx_limit=None, tx_use_coverage=True, tx_account="attacker"):
        owner_account = self.create_account(balance=1000)
        attacker_account = self.create_account(balance=1000)
        with open(solidity_filename) as f:
            contract_account = self.solidity_create_contract(f, contract_name=contract_name, owner=owner_account, args=(None, None, None, None))

        if tx_account == "attacker":
            tx_account = attacker_account
        elif tx_account == "owner":
            tx_account = owner_account
        else:
            raise EthereumError('The account to perform the symbolic exploration of the contract should be either "attacker" or "owner"')

        def run_symbolic_tx():
            symbolic_data = self.make_symbolic_buffer(320)
            symbolic_value = self.make_symbolic_value()
            self.transaction(caller=tx_account,
                             address=contract_account,
                             data=symbolic_data,
                             value=symbolic_value)

        if contract_account is None:
            logger.info("Failed to create contract. Exception in constructor")
            self.finalize()
            return

        prev_coverage = 0
        current_coverage = 0

        while (current_coverage < 100 or not tx_use_coverage) and not self.is_shutdown():
            try:
                run_symbolic_tx()
            except NoAliveStates:
                break

            if tx_limit is not None:
                tx_limit -= 1
                if tx_limit == 0:
                    break
            if tx_use_coverage:
                prev_coverage = current_coverage
                current_coverage = self.global_coverage(contract_account)
                found_new_coverage = prev_coverage < current_coverage

                if not found_new_coverage:
                    break

    def run(self, **kwargs):
        ''' Run any pending transaction on any running state '''
        # Check if there is a pending transaction
        with self.locked_context('seth') as context:
            assert context['_pending_transaction'] is not None

            # there is no states added to the executor queue
            assert len(self._executor.list()) == 0

            for state_id in context['_saved_states']:
                self._executor.put(state_id)
            context['_saved_states'] = []

        # A callback will use _pending_transaction and issue the transaction
        # in each state (see load_state_callback)
        super(ManticoreEVM, self).run(**kwargs)

        with self.locked_context('seth') as context:
            if len(context['_saved_states']) == 1:
                self._initial_state = self._executor._workspace.load_state(context['_saved_states'][0], delete=True)
                context['_saved_states'] = []
                assert self._running_state_ids == [-1]

            # clear pending transcations. We are done.
            context['_pending_transaction'] = None

    def save(self, state, final=False):
        ''' Save a state in secondary storage and add it to running or final lists

            :param state: A manticore State
            :param final: True if state is final
            :returns: a state id

        '''
        # save the state to secondary storage
        state_id = self._executor._workspace.save_state(state)
        with self.locked_context('seth') as context:
            if final:
                # Keep it on a private list
                context['_final_states'].append(state_id)
            else:
                # Keep it on a private list
                context['_saved_states'].append(state_id)
        return state_id

    def load(self, state_id=None):
        ''' Load one of the running or final states.

            :param state_id: If None it assumes there is a single running state
            :type state_id: int or None
        '''
        state = None
        if state_id is None:
            #a single state was assumed
            if self.count_running_states() == 1:
                #Get the ID of the single running state
                state_id = self._running_state_ids[0]
            else:
                raise Exception("More than one state running.")

        if state_id == -1:
            state = self.initial_state
        else:
            state = self._executor._workspace.load_state(state_id, delete=False)
            #froward events from newly loaded object
            self._executor.forward_events_from(state, True)
        return state

    # Callbacks
    def _symbolic_sha3(self, state, data, known_hashes):
        ''' INTERNAL USE '''

        with self.locked_context('known_sha3', set) as known_sha3:
            state.platform._sha3.update(known_sha3)

    def _concrete_sha3(self, state, buf, value):
        ''' INTERNAL USE '''
        with self.locked_context('known_sha3', set) as known_sha3:
            known_sha3.add((str(buf), value))

    def _terminate_state_callback(self, state, state_id, e):
        ''' INTERNAL USE
            Every time a state finishes executing last transaction we save it in
            our private list
        '''
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
        if tx.result in {'REVERT', 'THROW', 'TXERROR'}:
            self.save(state, final=True)
        else:
            assert tx.result in {'SELFDESTRUCT', 'RETURN', 'STOP'}
            # if not a revert we save the state for further transactioning
            del state.context['processed']
            self.save(state)  # Add tu running states

    #Callbacks
    def _load_state_callback(self, state, state_id):
        ''' INTERNAL USE
            When a state was just loaded from stoage we do the pending transaction
        '''
        if state.context.get('processed', False):
            return
        world = state.platform
        state.context['processed'] = True
        with self.locked_context('seth') as context:
            # take current global transaction we need to apply to all running states
            ty, caller, address, value, data, price = context['_pending_transaction']

        txnum = len(world.human_transactions)

        # Replace any None by symbolic values
        if value is None:
            value = state.new_symbolic_value(256, label='tx%d_value' % txnum)
        if isinstance(data, tuple):
            if any(x is None for x in data):
                symbolic_data = state.constraints.new_array(index_bits=256, name='tx%d_data' % txnum, index_max=len(data))
                for i in range(len(data)):
                    if data[i] is not None:
                        symbolic_data[i] = data[i]
                data = symbolic_data
            else:
                data = bytearray(data)

        if ty == 'CALL':
            world.transaction(address=address, caller=caller, data=data, value=value, price=price)
        else:
            assert ty == 'CREATE_CONTRACT'
            world.create_contract(caller=caller, address=address, balance=value, init=data, price=price)

    def _did_evm_execute_instruction_callback(self, state, instruction, arguments, result_ref):
        ''' INTERNAL USE '''
        logger.debug("%s", state.platform.current_vm)
        #TODO move to a plugin
        at_init = state.platform.current_transaction.sort == 'CREATE'
        pc = instruction.offset
        if at_init:
            coverage_context_name = 'init_coverage'
        else:
            coverage_context_name = 'runtime_coverage'

        with self.locked_context(coverage_context_name, set) as coverage:
            coverage.add((state.platform.current_vm.address, pc))

        state.context.setdefault('evm.trace', []).append((state.platform.current_vm.address, pc, at_init))

    def _did_evm_read_code(self, state, offset, size):
        ''' INTERNAL USE '''
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset + size):
                code_data.add((state.platform.current_vm.address, i))

    def get_metadata(self, address):
        ''' Gets the solidity metadata for address.
            This is available only if address is a contract created from solidity
        '''
        return self.metadata.get(int(address))

    def register_detector(self, d):
        if not isinstance(d, Detector):
            raise Exception("Not a Detector")
        if d.name in self.detectors:
            raise Exception("Detector already registered")
        self.detectors[d.name] = d
        self.register_plugin(d)
        return d.name

    def unregister_detector(self, d):
        if not isinstance(d, (Detector, str)):
            raise Exception("Not a Detector")
        name = d
        if isinstance(d, Detector):
            name = d.name
        if name not in self.detectors:
            raise Exception("Detector not registered")
        d = self.detectors[name]
        del self.detectors[name]
        self.unregister_plugin(d)

    @property
    def workspace(self):
        return self._executor._workspace._store.uri

    def generate_testcase(self, state, name, message=''):
        self._generate_testcase_callback(state, name, message)

    def _generate_testcase_callback(self, state, name, message=''):
        '''
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        '''
        # workspace should not be responsible for formating the output
        # each object knows its secrets, each class should be able to report its
        # final state
        #super(ManticoreEVM, self)._generate_testcase_callback(state, name, message)
        # TODO(mark): Refactor ManticoreOutput to let the platform be more in control
        #  so this function can be fully ported to EVMWorld.generate_workspace_files.
        blockchain = state.platform

        def flagged(flag):
            return '(*)' if flag else ''
        testcase = self._output.testcase(name.replace(' ', '_'))
        logger.info("Generated testcase No. {} - {}".format(testcase.num, message + blockchain.last_transaction.result))

        local_findings = set()
        for detector in self.detectors.values():
            for address, pc, finding, at_init in detector.get_findings(state):
                if (address, pc, finding, at_init) not in local_findings:
                    local_findings.add((address, pc, finding, at_init))

        if len(local_findings):
            with testcase.open_stream('findings') as findings:
                for address, pc, finding, at_init in local_findings:
                    findings.write('Finding: %s\n' % finding)
                    findings.write('Contract: 0x%x\n' % address)
                    findings.write('EVM Program counter: %s%s\n' % (pc, at_init and " (at constructor)" or ""))
                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc, runtime=not at_init)
                        findings.write('Snippet:\n')
                        findings.write('\n'.join((' ' + x for x in src.split('\n'))))
                        findings.write('\n\n')

        with testcase.open_stream('summary') as summary:
            summary.write("Message: %s\n" % message)
            summary.write("Last exception: %s\n" % state.context['last_exception'])

            at_runtime = blockchain.last_transaction.sort != 'CREATE'
            address, offset, at_init = state.context['evm.trace'][-1]
            assert at_runtime != at_init

            #Last instruction if last tx vas valid
            if state.context['last_exception'].message != 'TXERROR':
                metadata = self.get_metadata(blockchain.last_transaction.address)
                if metadata is not None:
                    summary.write('Last instruction at contract %x offset %x\n' % (address, offset))
                    source_code_snippet = metadata.get_source_for(offset, at_runtime)
                    if source_code_snippet:
                        summary.write(source_code_snippet)
                    summary.write('\n')

            # Accounts summary
            is_something_symbolic = False
            summary.write("%d accounts.\n" % len(blockchain.accounts))
            for account_address in blockchain.accounts:
                is_account_address_symbolic = issymbolic(account_address)
                account_address = state.solve_one(account_address)
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
                '''if blockchain.has_storage(account_address):
                    summary.write("Storage:\n")
                    for offset, value in blockchain.get_storage_items(account_address):
                        is_storage_symbolic = issymbolic(offset) or issymbolic(value)
                        offset = state.solve_one(offset)
                        value = state.solve_one(value)
                        summary.write("\t%032x -> %032x %s\n" % (offset, value, flagged(is_storage_symbolic)))
                        is_something_symbolic = is_something_symbolic or is_storage_symbolic
                '''

                runtime_code = state.solve_one(blockchain.get_code(account_address))
                if runtime_code:
                    summary.write("Code:\n")
                    fcode = StringIO.StringIO(runtime_code)
                    for chunk in iter(lambda: fcode.read(32), b''):
                        summary.write('\t%s\n' % chunk.encode('hex'))
                    runtime_trace = set((pc for contract, pc, at_init in state.context['evm.trace'] if address == contract and not at_init))
                    summary.write("Coverage %d%% (on this state)\n" % calculate_coverage(runtime_code, runtime_trace))  # coverage % for address in this account/state
                summary.write("\n")

            if blockchain._sha3:
                summary.write("Known hashes:\n")
                for key, value in blockchain._sha3.items():
                    summary.write('%s::%x\n' % (key.encode('hex'), value))

            if is_something_symbolic:
                summary.write('\n\n(*) Example solution given. Value is symbolic and may take other values\n')

        # Transactions
        with testcase.open_stream('tx') as tx_summary:
            is_something_symbolic = False
            for tx in blockchain.transactions:  # external transactions
                tx_summary.write("Transactions Nr. %d\n" % blockchain.transactions.index(tx))

                # The result if any RETURN or REVERT
                tx_summary.write("Type: %s\n" % tx.sort)
                tx_summary.write("From: 0x%x %s\n" % (state.solve_one(tx.caller), flagged(issymbolic(tx.caller))))
                tx_summary.write("To: 0x%x %s\n" % (state.solve_one(tx.address), flagged(issymbolic(tx.address))))
                tx_summary.write("Value: %d %s\n" % (state.solve_one(tx.value), flagged(issymbolic(tx.value))))
                tx_data = state.solve_one(tx.data)
                tx_summary.write("Data: %s %s\n" % (binascii.hexlify(tx_data), flagged(issymbolic(tx.data))))
                if tx.return_data is not None:
                    return_data = state.solve_one(tx.return_data)
                    tx_summary.write("Return_data: %s %s\n" % (binascii.hexlify(return_data), flagged(issymbolic(tx.return_data))))
                metadata = self.get_metadata(tx.address)
                if tx.sort == 'CALL':
                    if metadata is not None:
                        function_id = tx.data[:4]  # hope there is enough data
                        function_id = binascii.hexlify(state.solve_one(function_id))
                        signature = metadata.get_func_signature(function_id)
                        # FIXME Can this fail when absurd encoding? \/
                        function_name, arguments = ABI.parse(signature, tx.data)

                        return_data = None
                        if tx.result == 'RETURN':
                            ret_types = metadata.get_func_return_types(function_id)
                            return_data = ABI.parse(ret_types, tx.return_data)  # function return

                        tx_summary.write('\n')
                        tx_summary.write("Function call:\n")
                        tx_summary.write("%s(" % state.solve_one(function_name))
                        tx_summary.write(','.join(map(repr, map(state.solve_one, arguments))))
                        is_argument_symbolic = any(map(issymbolic, arguments))
                        is_something_symbolic = is_something_symbolic or is_argument_symbolic
                        tx_summary.write(') -> %s %s\n' % (tx.result, flagged(is_argument_symbolic)))

                        if return_data is not None:
                            is_return_symbolic = any(map(issymbolic, return_data))
                            return_values = tuple(map(state.solve_one, return_data))
                            if len(return_values) == 1:
                                return_values = return_values[0]

                            tx_summary.write('return: %r %s\n' % (return_values, flagged(is_return_symbolic)))
                            is_something_symbolic = is_something_symbolic or is_return_symbolic

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
                printable_bytes = ''.join(filter(lambda c: c in string.printable, map(chr, solved_memlog)))

                logs_summary.write("Address: %x\n" % log_item.address)
                logs_summary.write("Memlog: %s (%s) %s\n" % (binascii.hexlify(solved_memlog), printable_bytes, flagged(is_log_symbolic)))
                logs_summary.write("Topics:\n")
                for i, topic in enumerate(log_item.topics):
                    logs_summary.write("\t%d) %x %s" % (i, state.solve_one(topic), flagged(issymbolic(topic))))

        with testcase.open_stream('constraints') as smt_summary:
            smt_summary.write(str(state.constraints))

        with testcase.open_stream('pkl') as statef:
            try:
                statef.write(pickle.dumps(state, 2))
            except RuntimeError:
                # recursion exceeded. try a slower, iterative solution
                from .utils import iterpickle
                logger.debug("Using iterpickle to dump state")
                statef.write(iterpickle.dumps(state, 2))

        with testcase.open_stream('trace') as f:
            self._emit_trace_file(f, state.context['evm.trace'])
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
        q = Queue()
        map(q.put, self._all_state_ids)

        def f(q):
            try:
                while True:
                    state_id = q.get_nowait()
                    state_id = self._terminate_state_id(state_id)
                    st = self.load(state_id)
                    logger.debug("Generating testcase for state_id %d", state_id)
                    self._generate_testcase_callback(st, 'test', '')
            except EmptyQueue:
                pass

        ps = []

        for _ in range(self._config_procs):
            p = Process(target=f, args=(q,))
            p.start()
            ps.append(p)

        for p in ps:
            p.join()

        #global summary
        if len(self.global_findings):
            with self._output.save_stream('global.findings') as global_findings:
                for address, pc, finding, at_init in self.global_findings:
                    global_findings.write('- %s -\n' % finding)
                    global_findings.write('\tContract: %s\n' % address)
                    global_findings.write('\tEVM Program counter: %s%s\n' % (pc, at_init and " (at constructor)" or ""))

                    md = self.get_metadata(address)
                    if md is not None:
                        src = md.get_source_for(pc, runtime=not at_init)
                        global_findings.write('\tSolidity snippet:\n')
                        global_findings.write('\n'.join(('\t ' + x for x in src.split('\n'))))
                        global_findings.write('\n\n')

        with self._output.save_stream('global.summary') as global_summary:
            # (accounts created by contract code are not in this list )
            global_summary.write("Global runtime coverage:\n")
            for address in self.contract_accounts:
                global_summary.write("%x: %d%%\n" % (address, self.global_coverage(address)))

            md = self.get_metadata(address)
            if md is not None and len(md.warnings) > 0:
                global_summary.write('\n\nCompiler warnings for %s:\n' % md.name)
                global_summary.write(md.warnings)

        for address, md in self.metadata.items():
            with self._output.save_stream('global_%s.sol' % md.name) as global_src:
                global_src.write(md.source_code)
            with self._output.save_stream('global_%s_runtime.bytecode' % md.name) as global_runtime_bytecode:
                global_runtime_bytecode.write(md.runtime_bytecode)
            with self._output.save_stream('global_%s_init.bytecode' % md.name) as global_init_bytecode:
                global_init_bytecode.write(md.init_bytecode)

            with self._output.save_stream('global_%s.runtime_asm' % md.name) as global_runtime_asm:
                runtime_bytecode = md.runtime_bytecode

                with self.locked_context('runtime_coverage') as seen:

                    count, total = 0, 0
                    for i in evm.EVMAsm.disassemble_all(runtime_bytecode):
                        if (address, i.offset) in seen:
                            count += 1
                            global_runtime_asm.write('*')
                        else:
                            global_runtime_asm.write(' ')

                        global_runtime_asm.write('%4x: %s\n' % (i.offset, i))
                        total += 1

            with self._output.save_stream('global_%s.init_asm' % md.name) as global_init_asm:
                with self.locked_context('init_coverage') as seen:
                    count, total = 0, 0
                    for i in evm.EVMAsm.disassemble_all(md.init_bytecode):
                        if (address, i.offset) in seen:
                            count += 1
                            global_init_asm.write('*')
                        else:
                            global_init_asm.write(' ')

                        global_init_asm.write('%4x: %s\n' % (i.offset, i))
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
        with self.locked_context('seth') as seth_context:
            seth_context['_saved_states'] = []
        with self.locked_context('seth') as seth_context:
            seth_context['_final_states'] = []

        logger.info("Results in %s", self.workspace)

    def global_coverage(self, account_address):
        ''' Returns code coverage for the contract on `account_address`.
            This sums up all the visited code lines from any of the explored
            states.
        '''
        account_address = int(account_address)
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
