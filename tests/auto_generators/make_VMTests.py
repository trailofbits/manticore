"""
This script generates VMTests that are used to check EVM's Frontier fork correctness.

$ cd manticore/tests/ethereum
$ git clone https://github.com/ethereum/tests --depth=1
$ for i in tests/VMTests/*; do python ../auto_generators/make_VMTests.py $i > ./VMTests/test_`basename $i`.py; done
$ rm -rf ./tests  # cleanup/remove the ethereum/tests repo
"""
import json
import os
import sys
from binascii import unhexlify

import hashlib
import pyevmasm as EVMAsm


def gen_test(testcase, filename, skip):
    output = ''
    if skip:
        output += '''    @unittest.skip('Gas or performance related')\n'''

    testname = (os.path.split(filename)[1].replace('-', '_')).split('.')[0]
    bytecode = unhexlify(testcase['exec']['code'][2:])
    disassemble = ''
    try:
        # add silent=True when evmasm supports it
        disassemble = '\n                  '.join(EVMAsm.disassemble(bytecode).split('\n'))
    except Exception as e:
        pass

    with open(filename, 'rb') as f:
        sha256sum = hashlib.sha256(f.read()).hexdigest()

    output += f'''
    def test_{testname}(self):
        """
        Textcase taken from https://github.com/ethereum/tests
        File: {os.path.split(filename)[1]}
        sha256sum: {sha256sum}
        Code:     {disassemble}
        """    
    '''
    env = testcase['env']

    gaslimit = int(env['currentGasLimit'], 0)
    blocknumber = int(env['currentNumber'], 0)
    timestamp = int(env['currentTimestamp'], 0)
    difficulty = int(env['currentDifficulty'], 0)
    coinbase = int(env['currentCoinbase'], 0)
    output += f'''
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber={blocknumber}, timestamp={timestamp}, difficulty={difficulty},
                             coinbase={coinbase}, gaslimit={gaslimit})
    '''

    for address, account in testcase['pre'].items():
        account_address = int(address, 0)
        account_code = account['code'][2:]
        account_nonce = int(account['nonce'], 0)
        account_balance = int(account['balance'], 0)

        output += f'''
        bytecode = unhexlify('{account_code}')
        world.create_account(
            address={hex(account_address)},
            balance={account_balance},
            code=bytecode,
            nonce={account_nonce}
        )'''

        for key, value in account['storage'].items():
            output += f'''
        world.set_storage_data({hex(account_address)}, {key}, {value})'''

    address = int(testcase['exec']['address'], 0)
    caller = int(testcase['exec']['caller'], 0)
    code = testcase['exec']['code'][2:]
    calldata = testcase['exec']['data'][2:]
    gas = int(testcase['exec']['gas'], 0)
    price = int(testcase['exec']['gasPrice'], 0)
    origin = int(testcase['exec']['origin'], 0)
    value = int(testcase['exec']['value'], 0)

    # Need to check if origin is diff from caller. we do not support those tests
    assert origin == caller, "test type not supported"
    assert testcase['pre']['0x{:040x}'.format(address)]['code'][2:] == code, "test type not supported"

    output += f'''
        address = {hex(address)}
        price = {hex(price)}'''

    if calldata:
        output += f'''
        data = unhexlify('{calldata}')'''
    else:
        output += f"""
        data = ''"""

    output += f'''
        caller = {hex(caller)}
        value = {value}
        gas = {gas}

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
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')'''

    if 'post' not in testcase:
        output += '''
        #If test end in exception check it here
        self.assertTrue(result == 'THROW')'''
    else:

        for address, account in testcase['post'].items():
            account_address = int(address, 0)
            account_code = account['code'][2:]
            account_nonce = int(account['nonce'], 0)
            account_balance = int(account['balance'], 0)

            output += f'''
        # Add pos checks for account {hex(account_address)}
        # check nonce, balance, code
        self.assertEqual(world.get_nonce({hex(account_address)}), {account_nonce})
        self.assertEqual(to_constant(world.get_balance({hex(account_address)})), {account_balance})
        self.assertEqual(world.get_code({hex(account_address)}), unhexlify('{account_code}'))'''

        if account['storage']:
            output += '''
        #check storage'''

            for key, value in account['storage'].items():
                output += f'''
        self.assertEqual(to_constant(world.get_storage_data({hex(account_address)}, {key})), {value})'''

        output += f'''
        # check outs
        self.assertEqual(returndata, unhexlify('{testcase['out'][2:]}'))'''

        output += '''
        # check logs
        logs = [Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs]
        data = rlp.encode(logs)'''
        output += f'''
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '{testcase['logs'][2:]}')
        '''

        output += f'''
        # test used gas
        self.assertEqual(to_constant(world.current_vm.gas), {int(testcase['gas'], 0)})'''

    return output


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit()

    filename_or_folder = os.path.abspath(sys.argv[1])

    print(f'''"""DO NOT MODIFY: Test `{filename_or_folder}` generated with make_VMTests.py"""
import unittest
from binascii import unhexlify

import rlp
import sha3
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)

from manticore.core.smtlib import ConstraintSet
from manticore.core.smtlib.visitors import to_constant
from manticore.platforms import evm


class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_{os.path.splitext(os.path.basename(filename_or_folder))[0]}(unittest.TestCase):
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
        evm.DEFAULT_FORK = cls.SAVED_DEFAULT_FORK''')


    def disabled(test):
        if 'Performance' in test:
            return True
        return False


    if os.path.isdir(filename_or_folder):
        folder = filename_or_folder
        for filename in os.listdir(folder):
            if not filename.endswith('.json'):
                continue

            filename = os.path.join(folder, filename)
            testcase = dict(json.loads(open(filename).read()))
            for name, testcase in testcase.items():
                print(gen_test(testcase, filename, disabled(filename)))
    else:
        filename = os.path.abspath(filename_or_folder)
        testcase = dict(json.loads(open(filename).read()))
        for name, testcase in testcase.items():
            print(gen_test(testcase, filename, disabled(filename)))

    print('''

if __name__ == '__main__':
    unittest.main()''')
