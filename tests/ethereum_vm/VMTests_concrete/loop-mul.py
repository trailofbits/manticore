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


    def test_loop-mul_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmPerformance/loop-mulFiller.json 
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
            PUSH1 0x60
            PUSH1 0x40
            MSTORE
            PUSH1 0xe0
            PUSH1 0x2
            EXP
            PUSH1 0x0
            CALLDATALOAD
            DIV
            PUSH4 0xeb8ac921
            DUP2
            EQ
            PUSH1 0x1c
            JUMPI
            JUMPDEST
            PUSH1 0x2
            JUMP
            JUMPDEST
            CALLVALUE
            PUSH1 0x2
            JUMPI
            PUSH1 0x64
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x0
            PUSH8 0x5851f42d4c957f2d
            PUSH8 0x14057b7ef767814f
            DUP3
            DUP1
            JUMPDEST
            PUSH1 0x0
            DUP7
            EQ
            PUSH1 0x76
            JUMPI
            POP
            POP
            SWAP4
            DUP2
            MUL
            DUP5
            ADD
            DUP1
            DUP3
            MUL
            DUP6
            ADD
            DUP1
            DUP3
            MUL
            SWAP6
            PUSH1 0x0
            NOT
            SWAP6
            SWAP1
            SWAP6
            ADD
            SWAP5
            SWAP2
            SWAP1
            PUSH1 0x3f
            JUMP
            JUMPDEST
            PUSH1 0x40
            DUP1
            MLOAD
            SWAP2
            DUP3
            MSTORE
            MLOAD
            SWAP1
            DUP2
            SWAP1
            SUB
            PUSH1 0x20
            ADD
            SWAP1
            RETURN
            JUMPDEST
            POP
            SWAP5
            SWAP6
            SWAP5
            POP
            POP
            POP
            POP
            POP
            JUMP
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=100000000000000000000000, 
                         code=unhexlify('606060405260e060020a6000350463eb8ac9218114601c575b6002565b3460025760646004356024356000675851f42d4c957f2d6714057b7ef767814f82805b600086146076575050938102840180820285018082029560001995909501949190603f565b60408051918252519081900360200190f35b50949594505050505056'), 
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
                      value=0,
                      data=b'\xeb\x8a\xc9!^\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xee\xed\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00',
                      gas=1000000000000,
                      price=12)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0x071055da)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7fffffffab3bf9b8)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d67a38c0638)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x152d02c7e14af6800000)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('606060405260e060020a6000350463eb8ac9218114601c575b6002565b3460025760646004356024356000675851f42d4c957f2d6714057b7ef767814f82805b600086146076575050938102840180820285018082029560001995909501949190603f565b60408051918252519081900360200190f35b50949594505050505056'))

if __name__ == '__main__':
    unittest.main()