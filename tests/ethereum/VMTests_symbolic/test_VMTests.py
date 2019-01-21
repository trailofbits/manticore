"""DO NOT MODIFY: Tests generated from `VMTests/vmTests` with make_VMTests.py"""
import unittest
from binascii import unhexlify

import rlp
import sha3
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)

from manticore.core.smtlib import ConstraintSet, Z3Solver  # Ignore unused import in non-symbolic tests!
from manticore.core.smtlib.visitors import to_constant
from manticore.platforms import evm


class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_vmTests(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None

    SAVED_DEFAULT_FORK = evm.DEFAULT_FORK

    @classmethod
    def setUpClass(cls):
        evm.DEFAULT_FORK = 'frontier'

    @classmethod
    def tearDownClass(cls):
        evm.DEFAULT_FORK = cls.SAVED_DEFAULT_FORK

    def test_suicide(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: suicide.json
        sha256sum: 1aa0a61de3c9576faf6ac4f002626210a5315d3132d032162b2934d304a60c1f
        Code:     CALLER
                  SELFDESTRUCT
        """    
    
        solver = Z3Solver()

        def solve(val):
            results = solver.get_all_values(constraints, val)
            # We constrain all values to single values!
            self.assertEqual(len(results), 1)
            return results[0]

        constraints = ConstraintSet()

        blocknumber = constraints.new_bitvec(256, name='blocknumber')
        constraints.add(blocknumber == 0)

        timestamp = constraints.new_bitvec(256, name='timestamp')
        constraints.add(timestamp == 1)

        difficulty = constraints.new_bitvec(256, name='difficulty')
        constraints.add(difficulty == 256)

        coinbase = constraints.new_bitvec(256, name='coinbase')
        constraints.add(coinbase == 244687034288125203496486448490407391986876152250)

        gaslimit = constraints.new_bitvec(256, name='gaslimit')
        constraints.add(gaslimit == 1000000)

        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    
        acc_addr = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        acc_code = unhexlify('33ff')
            
        acc_balance = constraints.new_bitvec(256, name='balance_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_balance == 100000000000000000000000)

        acc_nonce = constraints.new_bitvec(256, name='nonce_0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6')
        constraints.add(acc_nonce == 0)

        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)

        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        price = constraints.new_bitvec(256, name='price')
        constraints.add(price == 100000000000000)

        value = constraints.new_bitvec(256, name='value')
        constraints.add(value == 1000000000000000000)

        gas = constraints.new_bitvec(256, name='gas')
        constraints.add(gas == 100000)

        data = ''
        # open a fake tx, no funds send
        world._open_transaction('CALL', address, price, data, caller, value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), 0)
        self.assertEqual(solve(world.block_gaslimit()), 1000000)
        self.assertEqual(solve(world.block_timestamp()), 1)
        self.assertEqual(solve(world.block_difficulty()), 256)
        self.assertEqual(solve(world.block_coinbase()), 244687034288125203496486448490407391986876152250)

        # Add post checks for account 0xcd1722f3947def4cf144679da39c4c32bdc35681
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce(0xcd1722f3947def4cf144679da39c4c32bdc35681)), 0)
        self.assertEqual(solve(world.get_balance(0xcd1722f3947def4cf144679da39c4c32bdc35681)), 100000000000000000000000)
        self.assertEqual(world.get_code(0xcd1722f3947def4cf144679da39c4c32bdc35681), unhexlify(''))
        # check outs
        self.assertEqual(returndata, unhexlify(''))
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

        # test used gas
        self.assertEqual(solve(world.current_vm.gas), 99998)


if __name__ == '__main__':
    unittest.main()
