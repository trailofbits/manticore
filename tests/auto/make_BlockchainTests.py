#!/usr/bin/env python

import argparse
import sys
import os
import json
from binascii import hexlify, unhexlify
from collections import defaultdict
import hashlib

DEFAULT_FORK = "Byzantium"


def gen_test(json_test_case, file_name, skip):
    output = ''
    print(file_name)
    if skip:
        output += '''    @unittest.skip('Gas or performance related')\n'''

    test_name = (os.path.split(os.path.basename(file_name))[1].replace('-', '_')).split('.')[0]
    sha256sum = hashlib.sha256(open(file_name, 'rb').read()).hexdigest()

    output += f"""
    def test_{test_name}(self):
        '''
            Test case taken from https://github.com/ethereum/tests
            File: {file_name}
            sha256sum: {sha256sum}
        '''    
    """

    #  pre-state setup
    block_headers = [x for x in json_test_case['blocks'] if 'blockHeader' in x]
    if len(block_headers) != 1:
        print(block_headers)
        print(json_test_case)
        import sys
        sys.exit(1)

    env = block_headers[0]['blockHeader']
    print(env)
    gas_limit = int(env['gasLimit'], 0)
    block_number = int(env['number'], 0)
    timestamp = int(env['timestamp'], 0)
    difficulty = int(env['difficulty'], 0)
    coinbase = int(env['coinbase'], 0)
    output += f'''
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints, block_number={block_number}, timestamp={timestamp}, difficulty={difficulty}, coinbase={coinbase}, gas_limit={gas_limit})
        transaction_results = list()
    '''

    for address, account in json_test_case['pre'].items():
        account_address = int(address, 0)
        account_code = account['code'][2:]
        account_nonce = int(account['nonce'], 0)
        account_balance = int(account['balance'], 0)

        output += f'''
        account_address = {hex(account_address)}
        bytecode = unhexlify('{account_code}')
        world.create_account(address={hex(account_address)},
                             balance={account_balance},
                             code=bytecode,
                             nonce={account_nonce}
                            )'''

        for key, value in account['storage'].items():
            output += f'''
        world.set_storage_data({hex(account_address)}, {key}, {value})'''

    for transaction in block_headers[0]['transactions']:
        call_data = transaction['data'][2:]
        if call_data != '':
            call_data = bytes.fromhex(call_data)
        else:
            call_data = bytes()

        gas = int(transaction['gasLimit'], 0)
        price = int(transaction['gasPrice'], 0)

        r = int(transaction['r'][2:], 16)
        s = int(transaction['s'][2:], 16)
        v = int(transaction['v'][2:], 16)

        to = transaction['to'][2:]

        value = int(transaction['value'][2:], 16)
        nonce = int(transaction['nonce'][2:], 16)

        from ethereum.transactions import Transaction
        print(f"nonce {nonce} gasprice {price} startgas {gas} to {to} value {value} data {call_data} v {v} r {r} s {s}")
        t = Transaction(nonce=nonce,
                        gasprice=price,
                        startgas=gas,
                        to=to,
                        value=value,
                        data=call_data,
                        v=v, r=r, s=s)

        address = t.sender
        print(address.hex())

        output += f'''
        address = {address.hex()}
        price = {hex(price)}'''

        if call_data:
            output += f'''
        data = unhexlify('{call_data}')'''
        else:
            output += f"""
        data = ''"""

        output += f'''
        caller = {address.hex()}
        value = {value}
        gas = {gas}

        # open a fake tx, no funds send
        world._open_transaction('CALL', to, price, data, caller, value, gas=gas)

        result = None
        return_data = b''
        try:
            while True:
                world.current_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                return_data = to_constant(e.data)
        
        transaction_results.append(return_data)
        '''

    for address, account in json_test_case['postState'].items():
        account_address = int(address, 0)
        account_code = account['code'][2:]
        account_nonce = int(account['nonce'], 0)
        account_balance = int(account['balance'], 0)

        output += f'''
    # Add postState checks for account {hex(account_address)}
    # check nonce, balance, code
    self.assertEqual(world.get_nonce({hex(account_address)}), {account_nonce})
    self.assertEqual(to_constant(world.get_balance({hex(account_address)})), {account_balance})
    self.assertEqual(world.get_code({hex(account_address)}), unhexlify('{account_code}'))'''

        if account['storage']:
            output += '''
    #  check storage'''

            for key, value in account['storage'].items():
                output += f'''
    self.assertEqual(to_constant(world.get_storage_data({hex(account_address)}, {key})), {value})'''

    return output


def test_header(test_origin):
    return f'''
    #  Taken from {test_origin}
    import struct
    import unittest
    import json
    import os
    import xmlrunner
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

    class EVMTest_{os.path.splitext(os.path.basename(test_origin))[0]}(unittest.TestCase):
        _multiprocess_can_split_ = True
        maxDiff=None 
    '''


def test_footer():
    return '''
    if __name__ == '__main__':
        unittest.main(testRunner = xmlrunner.XMLTestRunner(output='test-reports'))'''


def disabled(test):
    if 'Performance' in test:
        return True
    return False


def find_eth_tests(ethereum_tests_dir, fork):
    """
    Return a list of files that contain Ethereum test case for a given fork.

    :param ethereum_tests_dir: Root Ethereum tests dir. E.g. ~/github/ethereum/tests
    :param fork: Fork name. E.g. Byzantium.
    :return:
    """
    test_files = []

    for dirpath, dirnames, files in os.walk(os.path.join(ethereum_tests_dir, 'BlockchainTests')):
        for name in files:
            if name.lower().endswith('.json'):
                json_test = dict(json.loads(open(os.path.join(dirpath, name)).read()))
                if any(key.endswith(fork) for key in json_test.keys()):
                    test_files.append(os.path.join(dirpath, name))

    return test_files


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Manticore test generator for Ethereum BlockchainTests")
    parser.add_argument('-i', '--eth-tests-path', nargs='?', help='Path to Ethereum tests', required=True)
    parser.add_argument('-o', '--output-path', nargs='?', default='generated', help='Output path, default="."')
    parser.add_argument('-d', '--dry-run', default=False, action='store_true')
    parser.add_argument('-f', '--fork', default=DEFAULT_FORK, type=str,
                        help='Fork, default: byzantium. Possible: [pre-byzantium, byzantium, constantinople].'
                             'Also an unsigned block number is accepted to select the fork.')

    args = parser.parse_args(sys.argv[1:])

    if not os.path.isdir(os.path.join(args.eth_tests_path, 'BlockchainTests')):
        sys.stderr.write('Wrong Ethereum tests path. Please provide a root path for BlockchainTests folder.')
        sys.exit(1)

    accepted_forks = ['Byzantium', 'Constantinople', 'EIP150', 'EIP158', 'Frontier', 'Homestead']
    arg_fork = args.fork.title()
    if arg_fork not in accepted_forks:
        sys.stderr.write('Wrong fork name. Please provide one of %s.\n' % accepted_forks)
        sys.exit(1)
    else:
        fork = arg_fork

    filename_or_folder = args.eth_tests_path

    eth_test_files = find_eth_tests(args.eth_tests_path, arg_fork)

    generated_tests = defaultdict(list)

    for test_file in sorted(eth_test_files):
        relative_test_path = os.path.relpath(test_file, args.eth_tests_path)
        test_suite = os.path.dirname(relative_test_path)
        #   collect test cases, there should be one per fork but who knows...
        json_test = dict(json.loads(open(test_file).read()))
        for test_case_name in json_test.keys():
            if test_case_name.endswith(fork):
                generated_tests[test_suite].append(gen_test(json_test[test_case_name],
                                                            test_file, disabled(relative_test_path)))

    for test in generated_tests.keys():
        print(test_header)
        for test_case in generated_tests[test]:
            print(test_case)
        print(test_footer)
