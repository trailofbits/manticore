#!/usr/bin/env python

# EVM disassembler
from manticore.platforms.evm import *
from manticore.core.smtlib import *
from manticore.core.smtlib.visitors import *
from manticore.utils import log

# log.set_verbosity(9)
config.out_of_gas = 1


def printi(instruction):
    print(f"Instruction: {instruction}")
    print(f"\tdescription: {instruction.description}")
    print(f"\tgroup: {instruction.group}")
    print(f"\taddress: {instruction.offset}")
    print(f"\tsize: {instruction.size}")
    print(f"\thas_operand: {instruction.has_operand}")
    print(f"\toperand_size: {instruction.operand_size}")
    print(f"\toperand: {instruction.operand}")
    print(f"\tsemantics: {instruction.semantics}")
    print(f"\tpops: {instruction.pops}")
    print(f"\tpushes:", instruction.pushes)
    print(f"\tbytes: 0x{instruction.bytes.hex()}")
    print(f"\twrites to stack: {instruction.writes_to_stack}")
    print(f"\treads from stack: {instruction.reads_from_stack}")
    print(f"\twrites to memory: {instruction.writes_to_memory}")
    print(f"\treads from memory: {instruction.reads_from_memory}")
    print(f"\twrites to storage: {instruction.writes_to_storage}")
    print(f"\treads from storage: {instruction.reads_from_storage}")
    print(f"\tis terminator {instruction.is_terminator}")


constraints = ConstraintSet()


code = EVMAsm.assemble(
    """
    MSTORE
"""
)


data = constraints.new_array(index_bits=256, name="array")


class callbacks:
    initial_stack = []

    def will_execute_instruction(self, pc, instr):
        for i in range(len(evm.stack), instr.pops):
            e = constraints.new_bitvec(256, name=f"stack_{len(self.initial_stack)}")
            self.initial_stack.append(e)
            evm.stack.insert(0, e)


class DummyWorld:
    def __init__(self, constraints):
        self.balances = constraints.new_array(index_bits=256, value_bits=256, name="balances")
        self.storage = constraints.new_array(index_bits=256, value_bits=256, name="storage")
        self.origin = constraints.new_bitvec(256, name="origin")
        self.price = constraints.new_bitvec(256, name="price")
        self.timestamp = constraints.new_bitvec(256, name="timestamp")
        self.coinbase = constraints.new_bitvec(256, name="coinbase")
        self.gaslimit = constraints.new_bitvec(256, name="gaslimit")
        self.difficulty = constraints.new_bitvec(256, name="difficulty")
        self.number = constraints.new_bitvec(256, name="number")

    def get_balance(self, address):
        return self.balances[address]

    def tx_origin(self):
        return self.origin

    def tx_gasprice(self):
        return self.price

    def block_coinbase(self):
        return self.coinbase

    def block_timestamp(self):
        return self.timestamp

    def block_number(self):
        return self.number

    def block_difficulty(self):
        return self.difficulty

    def block_gaslimit(self):
        return self.gaslimit

    def get_storage_data(self, address, offset):
        # This works on a single account address
        return self.storage[offset]

    def set_storage_data(self, address, offset, value):
        self.storage[offset] = value

    def log(self, address, topics, memlog):
        pass

    def send_funds(self, address, recipient, value):
        orig = self.balances[address] - value
        dest = self.balances[recipient] + value
        self.balances[address] = orig
        self.balances[recipient] = dest


caller = constraints.new_bitvec(256, name="caller")
value = constraints.new_bitvec(256, name="value")

world = DummyWorld(constraints)
callbacks = callbacks()

# evm = world.current_vm
evm = EVM(constraints, 0x41424344454647484950, data, caller, value, code, world=world, gas=1000000)
evm.subscribe("will_execute_instruction", callbacks.will_execute_instruction)

print("CODE:")
while not issymbolic(evm.pc):
    print(f"\t {evm.pc} {evm.instruction}")
    try:
        evm.execute()
    except EndTx as e:
        print(type(e))
        break

# print translate_to_smtlib(arithmetic_simplifier(evm.stack[0]))
print(f"STORAGE = {translate_to_smtlib(world.storage)}")
print(f"MEM = {translate_to_smtlib(evm.memory)}")


for i in range(len(callbacks.initial_stack)):
    print(f"STACK[{i}] = {translate_to_smtlib(callbacks.initial_stack[i])}")
print("CONSTRAINTS:")
print(constraints)

print(
    f"PC: {translate_to_smtlib(evm.pc)} {solver.get_all_values(constraints, evm.pc, maxcnt=3, silent=True)}"
)
