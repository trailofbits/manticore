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


    def test_loop-mulmod-2M_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmPerformance/loop-mulmod-2MFiller.json 
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
            PUSH4 0xffffffff
            PUSH1 0xe0
            PUSH1 0x2
            EXP
            PUSH1 0x0
            CALLDATALOAD
            DIV
            AND
            PUSH4 0x15d42327
            DUP2
            EQ
            PUSH1 0x22
            JUMPI
            JUMPDEST
            PUSH1 0x0
            JUMP
            JUMPDEST
            CALLVALUE
            PUSH1 0x0
            JUMPI
            PUSH1 0x38
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x64
            CALLDATALOAD
            PUSH1 0x4a
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
            PUSH1 0x0
            DUP5
            DUP2
            JUMPDEST
            DUP4
            DUP2
            LT
            ISZERO
            PUSH1 0x64
            JUMPI
            DUP5
            DUP7
            DUP4
            MULMOD
            SWAP2
            POP
            JUMPDEST
            PUSH1 0x1
            ADD
            PUSH1 0x4f
            JUMP
            JUMPDEST
            DUP2
            SWAP3
            POP
            JUMPDEST
            POP
            POP
            SWAP5
            SWAP4
            POP
            POP
            POP
            POP
            JUMP
            STOP
            LOG1
            PUSH6 0x627a7a723058
            SHA3
            SIGNEXTEND
            INVALID
            MSTORE
            INVALID
            INVALID
            ORIGIN
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=100000000000000000000000, 
                         code=unhexlify('606060405263ffffffff60e060020a60003504166315d4232781146022575b6000565b346000576038600435602435604435606435604a565b60408051918252519081900360200190f35b600084815b838110156064578486830991505b600101604f565b8192505b50509493505050505600a165627a7a723058200b2f52fbc8327bac47da1762338f70ad17310de956a58bbbca8ee58378f357900029'), 
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
                      data=b"\x15\xd4#'\x8e\xda\xd8\xb5[\x15\x86\x80^\xa8\xc2E\xd8\xc1k\x06\xa5\x10+y\x1f\xc6\xeb`i71\xc0g{\xf5\x01\x1ch\xdb\x1c\x17\x9c\xd3Z\xb3\xfc`\xc67\x04\xaa\x7f\xcb\xea@\xf1\x97\x82\xb1a\x1a\xab\xa8g&\xa7hl\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x1e\x84\x80",
                      gas=1000000000000,
                      price=12)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0x07de8313)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7fffffffa191db0c)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d67ad3624e4)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x152d02c7e14af6800000)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('606060405263ffffffff60e060020a60003504166315d4232781146022575b6000565b346000576038600435602435604435606435604a565b60408051918252519081900360200190f35b600084815b838110156064578486830991505b600101604f565b8192505b50509493505050505600a165627a7a723058200b2f52fbc8327bac47da1762338f70ad17310de956a58bbbca8ee58378f357900029'))

if __name__ == '__main__':
    unittest.main()