"""DO NOT MODIFY: Tests generated from `tests/` with auto_generators/make_VMTests.py"""
import unittest
from binascii import unhexlify
from manticore import ManticoreEVM, Plugin
from manticore.utils import config
consts = config.get_group('core')
consts.mprocessing = consts.mprocessing.single
consts = config.get_group('evm')
consts.oog = 'pedantic'

class EVMTest(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None


    def test_fibonacci10_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmPerformance/fibonacci10Filler.json 
        """
        class UsedGas(Plugin):
            @property
            def used_gas(self):
                with self.locked_context() as ctx:
                    return ctx['test_used_gas']
            @used_gas.setter
            def used_gas(self, value):
                with self.locked_context() as ctx:
                    ctx['test_used_gas']=value

            def did_close_transaction_callback(self, state, tx):
                if tx.is_human:
                    self.used_gas = tx.used_gas
    
        used_gas_plugin = UsedGas()
        m = ManticoreEVM(workspace_url="mem:", plugins=(used_gas_plugin,))


        
        """
            PUSH1 0xe0
            PUSH1 0x2
            EXP
            PUSH1 0x0
            CALLDATALOAD
            DIV
            DUP1
            PUSH4 0x2839e928
            EQ
            PUSH1 0x1e
            JUMPI
            DUP1
            PUSH4 0x61047ff4
            EQ
            PUSH1 0x34
            JUMPI
            STOP
            JUMPDEST
            PUSH1 0x2a
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x47
            JUMP
            JUMPDEST
            DUP1
            PUSH1 0x0
            MSTORE
            PUSH1 0x20
            PUSH1 0x0
            RETURN
            JUMPDEST
            PUSH1 0x3d
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x99
            JUMP
            JUMPDEST
            DUP1
            PUSH1 0x0
            MSTORE
            PUSH1 0x20
            PUSH1 0x0
            RETURN
            JUMPDEST
            PUSH1 0x0
            DUP3
            PUSH1 0x0
            EQ
            PUSH1 0x54
            JUMPI
            PUSH1 0x5e
            JUMP
            JUMPDEST
            DUP2
            PUSH1 0x1
            ADD
            SWAP1
            POP
            PUSH1 0x93
            JUMP
            JUMPDEST
            DUP2
            PUSH1 0x0
            EQ
            PUSH1 0x69
            JUMPI
            PUSH1 0x7b
            JUMP
            JUMPDEST
            PUSH1 0x75
            PUSH1 0x1
            DUP5
            SUB
            PUSH1 0x1
            PUSH1 0x47
            JUMP
            JUMPDEST
            SWAP1
            POP
            PUSH1 0x93
            JUMP
            JUMPDEST
            PUSH1 0x90
            PUSH1 0x1
            DUP5
            SUB
            PUSH1 0x8c
            DUP6
            PUSH1 0x1
            DUP7
            SUB
            PUSH1 0x47
            JUMP
            JUMPDEST
            PUSH1 0x47
            JUMP
            JUMPDEST
            SWAP1
            POP
            JUMPDEST
            SWAP3
            SWAP2
            POP
            POP
            JUMP
            JUMPDEST
            PUSH1 0x0
            DUP2
            PUSH1 0x0
            EQ
            DUP1
            PUSH1 0xa9
            JUMPI
            POP
            DUP2
            PUSH1 0x1
            EQ
            JUMPDEST
            PUSH1 0xb0
            JUMPI
            PUSH1 0xb7
            JUMP
            JUMPDEST
            DUP2
            SWAP1
            POP
            PUSH1 0xcf
            JUMP
            JUMPDEST
            PUSH1 0xc1
            PUSH1 0x2
            DUP4
            SUB
            PUSH1 0x99
            JUMP
            JUMPDEST
            PUSH1 0xcb
            PUSH1 0x1
            DUP5
            SUB
            PUSH1 0x99
            JUMP
            JUMPDEST
            ADD
            SWAP1
            POP
            JUMPDEST
            SWAP2
            SWAP1
            POP
            JUMP
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=100000000000000000000000, 
                         code=unhexlify('60e060020a6000350480632839e92814601e57806361047ff414603457005b602a6004356024356047565b8060005260206000f35b603d6004356099565b8060005260206000f35b600082600014605457605e565b8160010190506093565b81600014606957607b565b60756001840360016047565b90506093565b609060018403608c85600186036047565b6047565b90505b92915050565b6000816000148060a95750816001145b60b05760b7565b81905060cf565b60c1600283036099565b60cb600184036099565b0190505b91905056'), 
                         nonce=0)
        
        m.create_account(address=0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b,
                         balance=9223372036854775792, 
                         code=b'', 
                         nonce=0)
        #coinbase
        m.create_account(address=0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba,
                         balance=0, 
                         code=b'', 
                         nonce=0)
        
        # Start a block
        self.assertEqual(m.count_all_states(), 1)
        m.start_block(blocknumber=0x01,
                      timestamp=0x03e8,
                      difficulty=0x020000,
                      coinbase=0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba,
                      gaslimit=0x7fffffffffffffff)


        m.transaction(caller=0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b,
                      address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                      value=11,
                      data=b'a\x04\x7f\xf4\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\n',
                      gas=100000,
                      price=12)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0xa16a)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7ffffffffff86eed)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d674ecf90f8)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x152d02c7e14af680000b)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60e060020a6000350480632839e92814601e57806361047ff414603457005b602a6004356024356047565b8060005260206000f35b603d6004356099565b8060005260206000f35b600082600014605457605e565b8160010190506093565b81600014606957607b565b60756001840360016047565b90506093565b609060018403608c85600186036047565b6047565b90505b92915050565b6000816000148060a95750816001145b60b05760b7565b81905060cf565b60c1600283036099565b60cb600184036099565b0190505b91905056'))

if __name__ == '__main__':
    unittest.main()