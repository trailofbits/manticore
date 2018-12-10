# Usage:
# git clone https://github.com/ethereum/tests
# for i in tests/VMTests/*; do python3.6 make_VMTests.py $i > $MANTICORE/tests/EVM/VMTests/eth_`basename $i`.py; done
#MANTICORE is manticore source folder
from io import StringIO
from binascii import unhexlify
import pyevmasm as EVMAsm
import hashlib

def gen_test(testcase, filename, skip):

    output = ''
    if skip:
        output += '''    @unittest.skip('Gas or performance related')\n'''

    testname = (os.path.split(filename)[1].replace('-','_')).split('.')[0]
    bytecode = unhexlify(testcase['exec']['code'][2:])
    disassemble = ''
    try:
        #add silent=True when evmasm supports it
        disassemble = '\n                  '.join(EVMAsm.disassemble(bytecode).split('\n'))
    except Exception as e:
        pass

    with open(filename 'rb') as f: 
        sha256sum = hashlib.sha256(f.read()).hexdigest()

    output += f"""
    def test_{testname}(self):
        '''
            Textcase taken from https://github.com/ethereum/tests
            File: {filename}
            sha256sum: {sha256sum}
            Code: {disassemble}
        '''    
    """
    env = testcase['env']

    gaslimit=int(env['currentGasLimit'], 0)
    blocknumber=int(env['currentNumber'], 0)
    timestamp=int(env['currentTimestamp'], 0)
    difficulty=int(env['currentDifficulty'], 0)
    coinbase=int(env['currentCoinbase'], 0)
    output += f'''
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber={blocknumber}, timestamp={timestamp}, difficulty={difficulty}, coinbase={coinbase}, gaslimit={gaslimit})
    '''

    for address, account in testcase['pre'].items():
        account_address = int(address, 0)
        account_code = account['code'][2:]
        account_nonce = int(account['nonce'], 0)
        account_balance = int(account['balance'], 0)

        output += f'''
        bytecode = unhexlify('{account_code}')
        world.create_account(address={hex(account_address)},
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


    #Need to check if origin is diff from caller. we do not support those tests
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

        result = None
        returndata = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = to_constant(e.data)
        except evm.StartTx as e:
            self.fail('This tests should not initiate an internal tx (no CALLs allowed)')'''

    if 'post' not in testcase:
        output +='''
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))'''
    else:

        for address, account in testcase['post'].items():
            account_address = int(address, 0)
            account_code = account['code'][2:]
            account_nonce = int(account['nonce'], 0)
            account_balance = int(account['balance'], 0)

            output += f'''
        #Add pos checks for account {hex(account_address)}
        #check nonce, balance, code
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
        #check outs
        self.assertEqual(returndata, unhexlify('{testcase['out'][2:]}'))'''

        output += '''
        #check logs
        data = rlp.encode([Log(unhexlify('{:040x}'.format(l.address)), l.topics, to_constant(l.memlog)) for l in world.logs])'''
        output += f'''
        self.assertEqual(sha3.keccak_256(data).hexdigest(), '{testcase['logs'][2:]}')
        '''

        output += f'''
        # test spent gas
        self.assertEqual(world.current_vm.gas, {int(testcase['gas'], 0)})'''

    return output

import sys, os, json
if __name__ == '__main__':
    filename_or_folder = os.path.abspath(sys.argv[1])
    
    


    print(f'''
#Taken from {filename_or_folder}
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
from manticore.core.smtlib.visitors import to_constant
import sha3
import rlp
from rlp.sedes import (
    CountableList,
    BigEndianInt,
    Binary,
)
class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]

evm.DEFAULT_FORK = "frontier"
class EVMTest_{os.path.splitext(os.path.basename(filename_or_folder))[0]}(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 
''')

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
