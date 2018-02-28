#!/usr/bin/env python

# EVM disassembler
from manticore.platforms.evm import *
from manticore.core.smtlib import *
from manticore.core.smtlib.visitors import *
from manticore.utils import log
#log.set_verbosity(9)


def printi(instruction):
    print 'Instruction: %s'% instruction
    print '\tdescription:', instruction.description
    print '\tgroup:', instruction.group
    print '\taddress:', instruction.offset
    print '\tsize:', instruction.size
    print '\thas_operand:', instruction.has_operand
    print '\toperand_size:', instruction.operand_size
    print '\toperand:', instruction.operand
    print '\tsemantics:', instruction.semantics
    print '\tpops:', instruction.pops
    print '\tpushes:', instruction.pushes
    print '\tbytes:', '0x'+instruction.bytes.encode('hex')
    print '\twrites to stack:', instruction.writes_to_stack
    print '\treads from stack:', instruction.reads_from_stack
    print '\twrites to memory:', instruction.writes_to_memory
    print '\treads from memory:', instruction.reads_from_memory
    print '\twrites to storage:', instruction.writes_to_storage
    print '\treads from storage:', instruction.reads_from_storage
    print '\tis terminator', instruction.is_terminator



constraints = ConstraintSet()
address = constraints.new_bitvec(256, name='address')
origin = constraints.new_bitvec(256, name='origin')
price = constraints.new_bitvec(256, name='price')
caller = constraints.new_bitvec(256, name='caller')
value = constraints.new_bitvec(256, name='value')
balance = constraints.new_bitvec(256, name='balance')


code = EVMAsm.assemble(
'''
PUSH1 0x60
PUSH1 0x40 
MSTORE 
PUSH1 0x0 
DUP1 
PUSH1 0x14 
PUSH2 0x100 
EXP
DUP2 
SLOAD 
DUP2 
PUSH1 0xFF 
MUL 
NOT 
AND 
SWAP1 
DUP4 
ISZERO 
ISZERO 
MUL 
OR 
SWAP1 
SSTORE 
POP 
CALLVALUE 
ISZERO 
PUSH2 0x29 
JUMPI 
'''
)


data = constraints.new_array(index_bits=256, name='array')
header = {'timestamp': constraints.new_bitvec(256, name='timestamp'),
          'coinbase': constraints.new_bitvec(256, name='coinbase'),
          'gaslimit': constraints.new_bitvec(256, name='gaslimit'),
          'difficulty': constraints.new_bitvec(256, name='difficulty'),
          'number': constraints.new_bitvec(256, name='number')
        }

class callbacks():
    initial_stack = []
    def will_execute_instruction(self, pc, instr):
        for i in range(len(evm.stack), instr.pops):
            e = constraints.new_bitvec(256, name='stack_%d'%len(self.initial_stack))
            self.initial_stack.append(e)
            evm.stack.append(e)

callbacks = callbacks()
world = EVMWorld(constraints)
address = world.create_account(balance=balance, code='')


evm = EVM(constraints, address, origin, price, data, caller, value, code, header, world=world, depth=0, gas=1000000)
evm.subscribe('will_execute_instruction', callbacks.will_execute_instruction)


print "CODE:"
while not issymbolic(evm.pc):
    print '\t',evm.pc, evm.instruction
    evm.execute()

#print translate_to_smtlib(arithmetic_simplifier(evm.stack[0]))
print "STORAGE =",  translate_to_smtlib(world.get_storage(address))
print "MEM =",  translate_to_smtlib(evm.memory)


for i in range(len(callbacks.initial_stack)):
    print "STACK[%d] ="%i,  translate_to_smtlib(callbacks.initial_stack[i])
print "CONSTRAINTS:"
print constraints


print "PC:", solver.get_all_values(constraints, evm.pc)

