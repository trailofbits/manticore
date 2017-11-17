#!/usr/bin/env python

# EVM disassembler
from manticore.platforms.evm import *

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


instruction = EVMAssembler.disassemble_one('\x60\x10')
printi(instruction)

instruction = EVMAssembler.assemble_one('PUSH1 0x10')
printi(instruction)

for instruction in EVMAssembler.disassemble_all('\x30\x31'):
    printi(instruction)

for instruction in EVMAssembler.assemble_all('ADDRESS\nBALANCE'):
    printi(instruction)


#High level simple assembler/disassembler

EVMAssembler.assemble(
                        """PUSH1 0x60
                           BLOCKHASH
                           MSTORE
                           PUSH1 0x2
                           PUSH2 0x100
                        """
                     )


print EVMAssembler.disassemble('0x606040526002610100')



