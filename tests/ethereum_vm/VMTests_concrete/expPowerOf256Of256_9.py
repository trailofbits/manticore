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


    def test_expPowerOf256Of256_9_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmArithmeticTest/expPowerOf256Of256_9Filler.json 
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
            PUSH1 0x9
            PUSH2 0x100
            EXP
            PUSH2 0x100
            EXP
            PUSH1 0x0
            SSTORE
            PUSH1 0x9
            PUSH1 0xff
            EXP
            PUSH2 0x100
            EXP
            PUSH1 0x1
            SSTORE
            PUSH1 0x9
            PUSH2 0x101
            EXP
            PUSH2 0x100
            EXP
            PUSH1 0x2
            SSTORE
            PUSH1 0x9
            PUSH2 0x100
            EXP
            PUSH1 0xff
            EXP
            PUSH1 0x3
            SSTORE
            PUSH1 0x9
            PUSH1 0xff
            EXP
            PUSH1 0xff
            EXP
            PUSH1 0x4
            SSTORE
            PUSH1 0x9
            PUSH2 0x101
            EXP
            PUSH1 0xff
            EXP
            PUSH1 0x5
            SSTORE
            PUSH1 0x9
            PUSH2 0x100
            EXP
            PUSH2 0x101
            EXP
            PUSH1 0x6
            SSTORE
            PUSH1 0x9
            PUSH1 0xff
            EXP
            PUSH2 0x101
            EXP
            PUSH1 0x7
            SSTORE
            PUSH1 0x9
            PUSH2 0x101
            EXP
            PUSH2 0x101
            EXP
            PUSH1 0x8
            SSTORE
            STOP
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=1000000000000000000, 
                         code=unhexlify('60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a60085500'), 
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
                      data=b'',
                      gas=1000000,
                      price=12)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0x024408)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7fffffffffe4cf85)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d674ee33060)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x0de0b6b3a764000b)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60096101000a6101000a600055600960ff0a6101000a60015560096101010a6101000a60025560096101000a60ff0a600355600960ff0a60ff0a60045560096101010a60ff0a60055560096101000a6101010a600655600960ff0a6101010a60075560096101010a6101010a60085500'))
            # check storage
            self.assertEqual(world.get_storage_data(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x05), 0x2e350d847ba73dc2099f83f532951c47269d9fd7e411b50bae00a9581f8900ff)
            self.assertEqual(world.get_storage_data(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x04), 0x48be09b6c6ae2aa660f1972125cecbb1038b5d236ecf766ba786e2c4e887feff)
            self.assertEqual(world.get_storage_data(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x07), 0xf387ed41c1050f9da667f429a3e8fb30b61a55ede97d7b8acd797a03cd89ff01)
            self.assertEqual(world.get_storage_data(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x03), 0x53017d8eb210db2c8cd4a299079ec55c33085514ff7f00000000000000000001)
            self.assertEqual(world.get_storage_data(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x08), 0x525696c22bb3ce00fd2e3f6bbb9b4ea1046a5e31fcff2fedf8f8c74d28890101)
            self.assertEqual(world.get_storage_data(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6, 0x06), 0x013ab9e1f0df89a184b4d07080b68fb921f7aa6aff8100000000000000000001)

if __name__ == '__main__':
    unittest.main()