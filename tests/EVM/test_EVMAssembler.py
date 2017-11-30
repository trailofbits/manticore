
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_Assembler(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_ADD_1(self):
        instruction = evm.EVMAsm.disassemble_one('\x60\x10')
        self.assertEqual( evm.EVMAsm.Instruction(0x60, 'PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.', 16, 0),
                          instruction)


        instruction = evm.EVMAsm.assemble_one('PUSH1 0x10')
        evm.EVMAsm.Instruction(0x60, 'PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.', 16, 0)
        
        instructions1 = evm.EVMAsm.disassemble_all('\x30\x31')
        instructions2 = evm.EVMAsm.assemble_all('ADDRESS\nBALANCE')
        self.assertTrue( all(a == b for a,b in zip(instructions1, instructions2)))

        #High level simple assembler/disassembler

        bytecode = evm.EVMAsm.assemble_hex(
                                """PUSH1 0x60
                                   BLOCKHASH
                                   MSTORE
                                   PUSH1 0x2
                                   PUSH2 0x100
                                """
                             )
        self.assertEqual(bytecode, '0x606040526002610100')

        asmcode =  evm.EVMAsm.disassemble_hex('0x606040526002610100')
        self.assertEqual(asmcode, '''PUSH1 0x60\nBLOCKHASH\nMSTORE\nPUSH1 0x2\nPUSH2 0x100''')




if __name__ == '__main__':
    unittest.main()
