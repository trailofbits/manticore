import hashlib
import logging
from contextlib import contextmanager

from ..core.smtlib import Operators, taint_with, get_taints, Constant
from ..utils.helpers import istainted, issymbolic
from ..core.plugin import Plugin


logger = logging.getLogger(__name__)


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
