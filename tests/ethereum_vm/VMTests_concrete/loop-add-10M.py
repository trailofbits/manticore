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


    def test_loop-add-10M_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmPerformance/loop-add-10MFiller.json 
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
            PUSH2 0x42
            JUMPI
            DUP1
            PUSH4 0x59e3e1ea
            EQ
            PUSH2 0x70
            JUMPI
            DUP1
            PUSH4 0xc4f8b9fb
            EQ
            PUSH2 0x9e
            JUMPI
            DUP1
            PUSH4 0xe01330bb
            EQ
            PUSH2 0xc9
            JUMPI
            JUMPDEST
            INVALID
            JUMPDEST
            CALLVALUE
            ISZERO
            PUSH2 0x4a
            JUMPI
            INVALID
            JUMPDEST
            PUSH2 0x5e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x64
            CALLDATALOAD
            PUSH2 0xf4
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
            CALLVALUE
            ISZERO
            PUSH2 0x78
            JUMPI
            INVALID
            JUMPDEST
            PUSH2 0x5e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x64
            CALLDATALOAD
            PUSH2 0x11e
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
            CALLVALUE
            ISZERO
            PUSH2 0xa6
            JUMPI
            INVALID
            JUMPDEST
            PUSH2 0x5e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH2 0x152
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
            CALLVALUE
            ISZERO
            PUSH2 0xd1
            JUMPI
            INVALID
            JUMPDEST
            PUSH2 0x5e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH2 0x179
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
            PUSH2 0x110
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
            PUSH2 0xf9
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
            JUMPDEST
            PUSH1 0x0
            DUP5
            DUP2
            JUMPDEST
            DUP4
            DUP2
            LT
            ISZERO
            PUSH2 0x110
            JUMPI
            DUP6
            DUP3
            DUP2
            ISZERO
            ISZERO
            PUSH2 0x136
            JUMPI
            INVALID
            JUMPDEST
            DIV
            DUP6
            ADD
            SWAP2
            POP
            JUMPDEST
            PUSH1 0x1
            ADD
            PUSH2 0x123
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
            JUMPDEST
            PUSH1 0x0
            DUP4
            DUP2
            JUMPDEST
            DUP4
            DUP2
            LT
            ISZERO
            PUSH2 0x16c
            JUMPI
            SWAP1
            DUP5
            ADD
            SWAP1
            JUMPDEST
            PUSH1 0x1
            ADD
            PUSH2 0x157
            JUMP
            JUMPDEST
            DUP2
            SWAP3
            POP
            JUMPDEST
            POP
            POP
            SWAP4
            SWAP3
            POP
            POP
            POP
            JUMP
            JUMPDEST
            PUSH1 0x0
            DUP4
            DUP2
            JUMPDEST
            DUP4
            DUP2
            LT
            ISZERO
            PUSH2 0x16c
            JUMPI
            SWAP1
            DUP5
            MUL
            SWAP1
            JUMPDEST
            PUSH1 0x1
            ADD
            PUSH2 0x17e
            JUMP
            JUMPDEST
            DUP2
            SWAP3
            POP
            JUMPDEST
            POP
            POP
            SWAP4
            SWAP3
            POP
            POP
            POP
            JUMP
            STOP
            LOG1
            PUSH6 0x627a7a723058
            SHA3
            MOD
            POP
            DUP2
            INVALID
            INVALID
            SWAP16
            INVALID
            INVALID
            INVALID
            INVALID
            SGT
            ORIGIN
            MSTORE
            ORIGIN
            COINBASE
            INVALID
            INVALID
            INVALID
            INVALID
            XOR
            DUP2
            LOG0
            PUSH6 0x29599a9c67d0
            INVALID
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=100000000000000000000000, 
                         code=unhexlify('606060405263ffffffff60e060020a60003504166315d42327811461004257806359e3e1ea14610070578063c4f8b9fb1461009e578063e01330bb146100c9575bfe5b341561004a57fe5b61005e6004356024356044356064356100f4565b60408051918252519081900360200190f35b341561007857fe5b61005e60043560243560443560643561011e565b60408051918252519081900360200190f35b34156100a657fe5b61005e600435602435604435610152565b60408051918252519081900360200190f35b34156100d157fe5b61005e600435602435604435610179565b60408051918252519081900360200190f35b600084815b83811015610110578486830991505b6001016100f9565b8192505b5050949350505050565b600084815b8381101561011057858281151561013657fe5b04850191505b600101610123565b8192505b5050949350505050565b600083815b8381101561016c57908401905b600101610157565b8192505b50509392505050565b600083815b8381101561016c57908402905b60010161017e565b8192505b505093925050505600a165627a7a72305820065081bd1e9fdffccd251332523241eaabd0fb1881a06529599a9c67d0a568e50029'), 
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
                      data=b'\xc4\xf8\xb9\xfb\x8e\xda\xd8\xb5[\x15\x86\x80^\xa8\xc2E\xd8\xc1k\x06\xa5\x10+y\x1f\xc6\xeb`i71\xc0g{\xf5\x01\xff\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xaa\xff\xff\xff\xff\xff\xff\xff\xff\xbb\xff\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x98\x96\x80',
                      gas=1000000000000,
                      price=12)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0x2161442f)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7ffffffe6f70cdbc)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d68df573234)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x152d02c7e14af6800000)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('606060405263ffffffff60e060020a60003504166315d42327811461004257806359e3e1ea14610070578063c4f8b9fb1461009e578063e01330bb146100c9575bfe5b341561004a57fe5b61005e6004356024356044356064356100f4565b60408051918252519081900360200190f35b341561007857fe5b61005e60043560243560443560643561011e565b60408051918252519081900360200190f35b34156100a657fe5b61005e600435602435604435610152565b60408051918252519081900360200190f35b34156100d157fe5b61005e600435602435604435610179565b60408051918252519081900360200190f35b600084815b83811015610110578486830991505b6001016100f9565b8192505b5050949350505050565b600084815b8381101561011057858281151561013657fe5b04850191505b600101610123565b8192505b5050949350505050565b600083815b8381101561016c57908401905b600101610157565b8192505b50509392505050565b600083815b8381101561016c57908402905b60010161017e565b8192505b505093925050505600a165627a7a72305820065081bd1e9fdffccd251332523241eaabd0fb1881a06529599a9c67d0a568e50029'))

if __name__ == '__main__':
    unittest.main()