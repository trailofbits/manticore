# Usage:
# for i in tests/VMTests/*; do python3.6 make_evmtests.py $i > $DESTINATION/eth_`basename $i`.py; done

from pprint import pformat
from io import StringIO
from binascii import unhexlify
import pyevmasm as EVMAsm
import hashlib


def pretty(value, htchar=' ', lfchar='\n', indent=0, width=100):
    nlch = lfchar + htchar * (indent + 1)
    if type(value) is dict:
        items = [
            nlch + repr(key) + ': ' + pretty(value[key], htchar, lfchar, indent +  1, width)
            for key in value
        ]
        return '{%s}' % (','.join(items) + lfchar + htchar * indent)
    elif type(value) is list:
        items = [
            nlch + pretty(item, htchar, lfchar, indent + 1, width)
            for item in value
        ]
        return '[%s]' % (','.join(items) + lfchar + htchar * indent)
    elif type(value) is tuple:
        items = [
            nlch + pretty(item, htchar, lfchar, indent + 1, width)
            for item in value
        ]
        return '(%s)' % (','.join(items) + lfchar + htchar * indent)
    elif type(value) in (str, str):
        if len(value) ==0:
            return repr(value)

        if width is not None and isinstance(value, str):
            width = width - indent
            width = max(1, width)
            o = []
            for pos in range(0, len(value), width): 
                o.append(repr(value[pos: pos+width]) )
            return ('\\' + lfchar + htchar * indent).join(o)
        return repr(value)
    else:
        return repr(value)

pprint = pretty
pp = pretty
def spprint(x, indent=0, width=None,**kwargs):
    if width is not None and isinstance(x, str):
        o = ''
        for pos in range(0, len(x), width): 
            o += ' '*indent + repr(x[pos: pos+width]) + '\\'
        return o
    x = pformat(x, indent=0)
    return (('\n'+' '*indent)).join(x.split('\n'))

def i(x):
    if isinstance(x, int):
        return x
    assert isinstance(x, str)
    if not x.startswith('0x'):
        x = '0x' + x
    return int(x, 0)

def gen_test(testcase, filename, skip):

    output = ''
    if skip:
        output += '''    @unittest.skip('Gas or performance related')\n'''

    testname = (os.path.split(filename)[1].replace('-','_')).split('.')[0]
    bytecode = unhexlify(testcase['exec']['code'][2:])
    disassemble = ''
    try:
        disassemble = '\n                  '.join(EVMAsm.disassemble(bytecode, silent=True).split('\n'))
    except:
        pass
    sha256sum = hashlib.sha256(open(filename, 'rb').read()).hexdigest()

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
    coinbase=int(env['currentCoinbase'],0)
    output += f'''
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, blocknumber={blocknumber}, timestamp={timestamp}, difficulty={difficulty}, coinbase={coinbase}, gaslimit={gaslimit})
    '''

    for address, account in testcase['pre'].items():
        account_address = i(address)
        account_code = account['code'][2:]
        account_nonce = i(account['nonce'])
        account_balance = i(account['balance'])

        output += f'''
        world.create_account(address={hex(account_address)},
                             balance={account_balance},
                             code=unhexlify('{account_code}'),
                            )'''

        for key, value in account['storage'].items():
            output += '''
        world.set_storage_data({account_address}, {key}, {value})'''

    address = int(testcase['exec']['address'], 0)
    caller = int(testcase['exec']['caller'], 0)
    code = testcase['exec']['code'][2:]
    calldata = testcase['exec']['data'][2:]
    gas = int(testcase['exec']['gas'], 0)
    price = int(testcase['exec']['gasPrice'], 0)
    origin = int(testcase['exec']['origin'], 0)
    value = int(testcase['exec']['value'], 0)


    #Need to check if origin is diff from caller. we do not support those tests
    assert origin==caller, "test type not supported"
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
        bytecode = world.get_code(address)
        gas = {gas}

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data'''

    if 'post' not in testcase:
        output +='''
        #If test end in exception ceck it here
        self.assertTrue(result in ('THROW'))'''
    else:
        final_gas = testcase['gas']
        output += f'''
        # test spent gas
        self.assertEqual(new_vm.gas, {final_gas})'''

        output += '''
        #check refund
        #check logs
        '''

        for address, account in testcase['post'].items():
            account_address = i(address)
            account_code = account['code'][2:]
            account_nonce = i(account['nonce'])
            account_balance = i(account['balance'])

            output += f'''
        #Add pos checks for account hex(account_address)
        account_address = {hex(account_address)}
        #check nonce
        self.assertEqual(world.get_nonce(account_address), {account_nonce})
        #check balance
        self.assertEqual(world.get_balance(account_address), {account_balance})
        #check code
        self.assertEqual(world.get_code(account_address), unhexlify('{account_code}'))'''

        if account['storage']:
            output += '''
        #check storage'''

            for key, value in account['storage'].items():
                output += f'''
        self.assertEqual(world.get_storage_data(account_address, {key}), {value})'''

    return output

import sys, os, json
if __name__ == '__main__':
    folder = os.path.abspath(sys.argv[1])
    
    print(f'''
#Taken from folder {folder}
import struct
import unittest
import json
import os
from binascii import unhexlify
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet

class EVMTest_{os.path.basename(folder)}(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 
''')

    for filename in os.listdir(folder):
        if not filename.endswith('.json'):
            continue

        testcase = dict(json.loads(open(os.path.join(folder,filename)).read()))
        skip = False
        if False:
            skip = True
        #print (testcase)
        for name, testcase in testcase.items():
            print(gen_test(testcase, os.path.join(folder,filename), skip))

    print('''
if __name__ == '__main__':
    unittest.main()''')
