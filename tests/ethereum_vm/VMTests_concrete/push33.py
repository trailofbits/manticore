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


    def test_push33_Istanbul(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: src/VMTestsFiller/vmPushDupSwapTest/push33Filler.json 
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
            PUSH1 0x65
            PUSH2 0x7d2
            PUSH3 0x4a0c7
            PUSH4 0x26921f4
            PUSH5 0xbc5588eb1
            PUSH6 0x372d0f1dca6e
            PUSH7 0x1ba1d901961c71
            PUSH8 0xc55f7bc23038e38
            PUSH9 0x56bc75e2d630fffff
            PUSH10 0x21e19e0c9bab2400001
            PUSH11 0x85d1c6e8050f0ea1c71bd
            PUSH12 0x688be36543f3c36e638e37a
            PUSH13 0x3d41f73d55d0d482ae5555537
            PUSH14 0xc76810d0fe03c91964d31c71c6f4
            PUSH15 0x615dd0360c07d931663b14e38e38b1
            PUSH16 0x2da3f99955a3adcf27ebb1caaaaaaa6e
            PUSH17 0x14ccba6a8bb1ed35bd86bf065c71c71c2b
            PUSH18 0x9491c5d4781b79c9009de6bfb8e38e38de8
            PUSH19 0x414a0f6fdec81304d4c563e740bffffffffa5
            PUSH20 0x118427b3b4a05bc8a8a4de845986800000000001
            PUSH21 0x6eb15e7331e727940d4ac54b7cdca1c71c71c71bd
            PUSH22 0x567a91c9fefc96ebaa626a22f98c5e638e38e38e37a
            PUSH23 0x32abd16c5b68006e15d5aa307e383f4e5555555555537
            PUSH24 0x1a6427bdc4f0d58eab5f48a3ec67f64e21c71c71c71c6f4
            PUSH25 0x80dd0a0c9b9ff2c2a0c740b06853a0a980ee38e38e38e38b1
            PUSH26 0x3c679cb5e8f2f9cb3b5d6652b0e7334f746faaaaaaaaaaaaa6e
            PUSH27 0x1b873815917ebb2bf3b890a1af495d6235bae3c71c71c71c71c2b
            PUSH28 0x7ae4cca96e1a55dfa49c85ad3c3e60e426b92fb8e38e38e38e38de8
            PUSH29 0x36018bf074e292bcc7d6c8bea0f9699443046178bffffffffffffffa5
            PUSH30 0xe7d34c64a9c85d4460dbbca87196b61618a4bd216800000000000000001
            PUSH31 0x5b901f48a5b994d6572502bc4ea43140486666416aa1c71c71c71c71c71bd
            PUSH32 0x47889870c178fc477414ea231d70467a388fffe31b4e638e38e38e38e38e37a
            STOP
        """
        m.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                         balance=100000000000000000000000, 
                         code=unhexlify('60656107d26204a0c763026921f4640bc5588eb165372d0f1dca6e661ba1d901961c71670c55f7bc23038e3868056bc75e2d630fffff69021e19e0c9bab24000016a085d1c6e8050f0ea1c71bd6b0688be36543f3c36e638e37a6c03d41f73d55d0d482ae55555376dc76810d0fe03c91964d31c71c6f46e615dd0360c07d931663b14e38e38b16f2da3f99955a3adcf27ebb1caaaaaaa6e7014ccba6a8bb1ed35bd86bf065c71c71c2b7109491c5d4781b79c9009de6bfb8e38e38de8720414a0f6fdec81304d4c563e740bffffffffa573118427b3b4a05bc8a8a4de8459868000000000017406eb15e7331e727940d4ac54b7cdca1c71c71c71bd750567a91c9fefc96ebaa626a22f98c5e638e38e38e37a76032abd16c5b68006e15d5aa307e383f4e55555555555377701a6427bdc4f0d58eab5f48a3ec67f64e21c71c71c71c6f478080dd0a0c9b9ff2c2a0c740b06853a0a980ee38e38e38e38b17903c679cb5e8f2f9cb3b5d6652b0e7334f746faaaaaaaaaaaaa6e7a01b873815917ebb2bf3b890a1af495d6235bae3c71c71c71c71c2b7b07ae4cca96e1a55dfa49c85ad3c3e60e426b92fb8e38e38e38e38de87c036018bf074e292bcc7d6c8bea0f9699443046178bffffffffffffffa57d0e7d34c64a9c85d4460dbbca87196b61618a4bd2168000000000000000017e05b901f48a5b994d6572502bc4ea43140486666416aa1c71c71c71c71c71bd7f047889870c178fc477414ea231d70467a388fffe31b4e638e38e38e38e38e37a00'), 
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
                      gas=320000,
                      price=12)
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, 0x5268)
            
            world.end_block()
            # Add post checks for account 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x01)
            self.assertEqual(world.get_balance(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), 0x7ffffffffffc2305)
            self.assertEqual(world.get_code(0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b), b'')
            # Add post checks for account 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x00)
            self.assertEqual(world.get_balance(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), 0x1bc16d674ecbdce0)
            self.assertEqual(world.get_code(0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba), b'')
            # Add post checks for account 0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x00)
            self.assertEqual(world.get_balance(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), 0x152d02c7e14af680000b)
            self.assertEqual(world.get_code(0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6), unhexlify('60656107d26204a0c763026921f4640bc5588eb165372d0f1dca6e661ba1d901961c71670c55f7bc23038e3868056bc75e2d630fffff69021e19e0c9bab24000016a085d1c6e8050f0ea1c71bd6b0688be36543f3c36e638e37a6c03d41f73d55d0d482ae55555376dc76810d0fe03c91964d31c71c6f46e615dd0360c07d931663b14e38e38b16f2da3f99955a3adcf27ebb1caaaaaaa6e7014ccba6a8bb1ed35bd86bf065c71c71c2b7109491c5d4781b79c9009de6bfb8e38e38de8720414a0f6fdec81304d4c563e740bffffffffa573118427b3b4a05bc8a8a4de8459868000000000017406eb15e7331e727940d4ac54b7cdca1c71c71c71bd750567a91c9fefc96ebaa626a22f98c5e638e38e38e37a76032abd16c5b68006e15d5aa307e383f4e55555555555377701a6427bdc4f0d58eab5f48a3ec67f64e21c71c71c71c6f478080dd0a0c9b9ff2c2a0c740b06853a0a980ee38e38e38e38b17903c679cb5e8f2f9cb3b5d6652b0e7334f746faaaaaaaaaaaaa6e7a01b873815917ebb2bf3b890a1af495d6235bae3c71c71c71c71c2b7b07ae4cca96e1a55dfa49c85ad3c3e60e426b92fb8e38e38e38e38de87c036018bf074e292bcc7d6c8bea0f9699443046178bffffffffffffffa57d0e7d34c64a9c85d4460dbbca87196b61618a4bd2168000000000000000017e05b901f48a5b994d6572502bc4ea43140486666416aa1c71c71c71c71c71bd7f047889870c178fc477414ea231d70467a388fffe31b4e638e38e38e38e38e37a00'))

if __name__ == '__main__':
    unittest.main()