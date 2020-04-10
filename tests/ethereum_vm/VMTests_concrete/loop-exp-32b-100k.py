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


    def test_loop-exp-32b-100k_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmPerformance/loop-exp-32b-100kFiller.json 
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
            PUSH4 0x3392ffc8
            DUP2
            EQ
            PUSH2 0x3f
            JUMPI
            DUP1
            PUSH4 0x3c77b95c
            EQ
            PUSH2 0x6a
            JUMPI
            DUP1
            PUSH4 0xce67bda6
            EQ
            PUSH2 0xc2
            JUMPI
            DUP1
            PUSH4 0xebbbe00b
            EQ
            PUSH2 0xe8
            JUMPI
            JUMPDEST
            PUSH2 0x2
            JUMP
            JUMPDEST
            CALLVALUE
            PUSH2 0x2
            JUMPI
            PUSH2 0x10e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x0
            DUP3
            DUP2
            JUMPDEST
            DUP4
            DUP2
            LT
            ISZERO
            PUSH2 0x120
            JUMPI
            SWAP1
            DUP6
            SWAP1
            EXP
            SWAP1
            PUSH1 0x1
            ADD
            PUSH2 0x55
            JUMP
            JUMPDEST
            CALLVALUE
            PUSH2 0x2
            JUMPI
            PUSH2 0x10e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x0
            DUP3
            DUP2
            JUMPDEST
            DUP4
            DUP2
            LT
            ISZERO
            PUSH2 0x120
            JUMPI
            SWAP1
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            DUP6
            SWAP1
            EXP
            SWAP1
            PUSH1 0x10
            ADD
            PUSH2 0x80
            JUMP
            JUMPDEST
            CALLVALUE
            PUSH2 0x2
            JUMPI
            PUSH2 0x10e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x0
            DUP1
            JUMPDEST
            DUP3
            DUP2
            LT
            ISZERO
            PUSH2 0x129
            JUMPI
            JUMPDEST
            PUSH1 0x1
            ADD
            PUSH2 0xd7
            JUMP
            JUMPDEST
            CALLVALUE
            PUSH2 0x2
            JUMPI
            PUSH2 0x10e
            PUSH1 0x4
            CALLDATALOAD
            PUSH1 0x24
            CALLDATALOAD
            PUSH1 0x44
            CALLDATALOAD
            PUSH1 0x0
            DUP1
            JUMPDEST
            DUP3
            DUP2
            LT
            ISZERO
            PUSH2 0x129
            JUMPI
            JUMPDEST
            PUSH1 0x10
            ADD
            PUSH2 0xfd
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
            SWAP4
            POP
            POP
            POP
            POP
            JUMP
            JUMPDEST
            POP
            SWAP2
            SWAP4
            SWAP3
            POP
            POP
            POP
            JUMP
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=100000000000000000000000, 
                         code=unhexlify('606060405260e060020a60003504633392ffc8811461003f5780633c77b95c1461006a578063ce67bda6146100c2578063ebbbe00b146100e8575b610002565b346100025761010e600435602435604435600082815b83811015610120579085900a90600101610055565b346100025761010e600435602435604435600082815b83811015610120579085900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a90601001610080565b346100025761010e6004356024356044356000805b82811015610129575b6001016100d7565b346100025761010e6004356024356044356000805b82811015610129575b6010016100fd565b60408051918252519081900360200190f35b50949350505050565b5091939250505056'), 
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
                      data=b'3\x92\xff\xc8\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00XQ\xf4-L\x95\x7f-\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x86\xa0',
                      gas=1000000000000,
                      price=2)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0x09eced70)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7fffffffec262510)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d6762a1dae0)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x152d02c7e14af6800000)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('606060405260e060020a60003504633392ffc8811461003f5780633c77b95c1461006a578063ce67bda6146100c2578063ebbbe00b146100e8575b610002565b346100025761010e600435602435604435600082815b83811015610120579085900a90600101610055565b346100025761010e600435602435604435600082815b83811015610120579085900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a85900a90601001610080565b346100025761010e6004356024356044356000805b82811015610129575b6001016100d7565b346100025761010e6004356024356044356000805b82811015610129575b6010016100fd565b60408051918252519081900360200190f35b50949350505050565b5091939250505056'))

if __name__ == '__main__':
    unittest.main()