"""
# This script generates tests to check Manticore EVM's correctness.

## Get the upstream tests:
git clone https://github.com/ethereum/tests

## Optionally, checkout commit, say, cfbcd15:
cd tests && git checkout cfbcd15 && cd ..

## Generate tests for DEFAULT_TEST_FORK:
python auto_generators/make_BlockchainTests.py tests

## Generate tests for, say, Istanbul:
python auto_generators/make_BlockchainTests.py tests Istanbul

## Run the tests with at 10 second timeout:
find tests_Byzantium -name '*.py' -exec timeout 10s python3 {} \;

## Alternatively, run the tests using pytest:
find tests_Byzantium -name '*.py' -exec timeout 10s pytest {} \;
"""
import json
import os
import sys
from binascii import unhexlify

import hashlib
import pyevmasm as EVMAsm

DEFAULT_TEST_FORK = "Istanbul"
DISASSEMBLE_FORK = DEFAULT_TEST_FORK.lower()

test_fork = DEFAULT_TEST_FORK

def gen_test(testcase, filename, symbolic):
    output = ""
    
    # Sanity checks

    # We don't use those!
    testcase.pop("_info")
    assert len(testcase.pop("callcreates", [])) == 0

    output += generate_pre_output(testcase, filename, symbolic)

    if "postState" not in testcase:
        output += """
        # If test end in exception check it here
        self.assertTrue(result == 'THROW')"""
    else:
        output += generate_post_output(testcase)

    return output

def generate_pre_output(testcase, filename, symbolic):
    testname = (os.path.split(filename)[1].replace("-", "_")).split(".")[0]

    with open(filename, "rb") as f:
        sha256sum = hashlib.sha256(f.read()).hexdigest()

    output = f'''
    def test_{testname}(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        File: {os.path.split(filename)[1]}
        sha256sum: {sha256sum}
        """
    '''

    if symbolic:
        output += """
        def solve(val):
            return self._solve(constraints, val)
"""
    else:
        output += '''
        def solve(val):
            """
            Those tests are **auto-generated** and `solve` is used in symbolic tests.
            So yes, this returns just val; it makes it easier to generate tests like this.
            """
            return to_constant(val)
'''

    blocks = [x for x in testcase['blocks'] if 'blockHeader' in x]
    if len(blocks) != 1:
        raise NotImplementedError("Test cases with multiple blocks are not supported yet.")

    env = blocks[0]['blockHeader']

    gaslimit = int(env["gasLimit"], 0)
    blocknumber = int(env["number"], 0)
    timestamp = int(env["timestamp"], 0)
    difficulty = int(env["difficulty"], 0)
    coinbase = int(env["coinbase"], 0)
    output += f"""
        constraints = ConstraintSet()
"""

    def format_bitvec(name, val, bits=256, symbolic_name=None):
        if symbolic_name is None:
            symbolic_name = name

        return f"""
        {name} = constraints.new_bitvec({bits}, name='{symbolic_name}')
        constraints.add({name} == {val})
"""

    def format_var(name, val):
        if name == 'coinbase':
            return f"""
        {name} = {hex(val)}"""

        return f"""
        {name} = {val}"""

    # Spawns/creates bitvectors in symbolic or pure variables in concrete
    formatter = format_bitvec if symbolic else format_var
    for var in ("blocknumber", "timestamp", "difficulty", "coinbase", "gaslimit"):
        output += formatter(var, locals()[var])

    output += f"""
        world = evm.EVMWorld(constraints, blocknumber=blocknumber, timestamp=timestamp, difficulty=difficulty,
                             coinbase=coinbase, gaslimit=gaslimit)
    """

    for address, account in testcase["pre"].items():
        assert account.keys() == {"code", "nonce", "balance", "storage"}

        account_address = int(address, 0)
        account_code = account["code"][2:]
        account_nonce = int(account["nonce"], 0)
        account_balance = int(account["balance"], 0)

        disassembly = ""
        try:
            # add silent=True when evmasm supports it
            disassembly = "\n            ".join(EVMAsm.disassemble(unhexlify(account_code)).split("\n"))
        except Exception as e:
            pass

        if symbolic:
            postfix = hex(account_address)
            output += f"""
        acc_addr = {hex(account_address)}
        acc_code = unhexlify('{account_code}')
            """
            output += format_bitvec(
                "acc_balance", account_balance, symbolic_name=f"balance_{postfix}"
            )
            output += format_bitvec("acc_nonce", account_nonce, symbolic_name=f"nonce_{postfix}")
        else:
            output += f"""
        acc_addr = {hex(account_address)}
        acc_code = unhexlify('{account_code}')
        ''' {disassembly}
        '''
        acc_balance = {account_balance}
        acc_nonce = {account_nonce}
"""

        output += f"""
        world.create_account(address=acc_addr, balance=acc_balance, code=acc_code, nonce=acc_nonce)
"""
        for key, value in account["storage"].items():
            if symbolic:
                postfix = hex(account_address) + "_" + key
                output += format_bitvec("key", key, symbolic_name=f"storage_key_{postfix}")
                output += format_bitvec("value", value, symbolic_name=f"storage_value_{postfix}")
                output += """
        world.set_storage_data(acc_addr, key, value)
"""
            else:
                output += f"""
        world.set_storage_data(acc_addr, {key}, {value})
"""

    for transaction in blocks[0]['transactions']:
        address = 0 if transaction["to"] == "" else int(transaction["to"], 16)
        calldata = unhexlify(transaction["data"][2:])
        gas = int(transaction["gasLimit"], 0)
        price = int(transaction["gasPrice"], 0)
        nonce = int(transaction["nonce"], 0)
        value = 0 if transaction["value"] == "0x" else int(transaction["value"], 0)
        r = int(transaction["r"], 0)
        s = int(transaction["s"], 0)
        v = int(transaction["v"], 0)
        assert transaction.keys() == {
            "to",
            "data",
            "gasLimit",
            "gasPrice",
            "nonce",
            "value",
            "r",
            "s",
            "v",
        }

        # pip install py-evm
        from eth.vm.forks.frontier.transactions import FrontierTransaction
        t = FrontierTransaction(nonce=nonce,
                        gas_price=price,
                        gas=gas,
                        to=unhexlify(transaction['to'][2:]), # Can be the empty string.
                        value=value,
                        data=calldata,
                        v=v,
                        r=r,
                        s=s
                       )
        caller = int.from_bytes(t.sender, "big")

        output += f"""
        address = {hex(address)}
        caller = {hex(caller)}"""

        if symbolic:
            postfix = hex(caller) + "_" + hex(r)
            output += format_bitvec("price", price, symbolic_name=f"price_{postfix}")
            output += format_bitvec("value", value, symbolic_name=f"value_{postfix}")
            output += format_bitvec("gas", gas, symbolic_name=f"gas_{postfix}")
        else:
            output += f"""
        price = {hex(price)}
        value = {value}
        gas = {gas}"""

        if calldata:
            if symbolic:
                output += f"""
        data = constraints.new_array(index_max={len(calldata)})
        constraints.add(data == {calldata})
"""
            else:
                output += f"""
        data = {calldata}"""
        else:
            output += f"""
        data = ''"""

        output += f"""
        # open a fake tx, no funds send
        world.start_transaction({'"CREATE"' if address == 0 else '"CALL"'}, address, price=price, data=data, caller=caller, value=value, gas=gas)

        # This variable might seem redundant in some tests - don't forget it is auto generated
        # and there are cases in which we need it ;)
        result, returndata = self._test_run(world)

        # World sanity checks - those should not change, right?
        self.assertEqual(solve(world.block_number()), {blocknumber})
        self.assertEqual(solve(world.block_gaslimit()), {gaslimit})
        self.assertEqual(solve(world.block_timestamp()), {timestamp})
        self.assertEqual(solve(world.block_difficulty()), {difficulty})
        self.assertEqual(solve(world.block_coinbase()), {hex(coinbase)})
"""

    return output


def generate_post_output(testcase):
    global coinbase

    blocks = [x for x in testcase['blocks'] if 'blockHeader' in x]
    coinbase = blocks[0]['blockHeader']["coinbase"]


    output = ""

    for address, account in testcase["postState"].items():
        if address == coinbase:
            continue
        assert account.keys() == {"code", "nonce", "balance", "storage"}

        account_address = int(address, 0)
        account_code = account["code"][2:]
        account_nonce = int(account["nonce"], 0)
        account_balance = int(account["balance"], 0)

        output += f"""
        # Add post checks for account {hex(account_address)}
        # check nonce, balance, code
        self.assertEqual(solve(world.get_nonce({hex(account_address)})), {account_nonce})
        self.assertEqual(solve(world.get_balance({hex(account_address)})), {account_balance})
        self.assertEqual(world.get_code({hex(account_address)}), unhexlify('{account_code}'))"""

    if account["storage"]:
        output += """
        # check storage"""

        for key, value in account["storage"].items():
            output += f"""
        self.assertEqual(solve(world.get_storage_data({hex(account_address)}, {key})), {value})"""

    return output


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit()

    symbolic = False
    if "--symbolic" in sys.argv:
        symbolic = True
        sys.argv.remove("--symbolic")

    folder = os.path.join(sys.argv[1], 'BlockchainTests')

    if not os.path.isdir(folder):
        sys.stderr.write('Wrong Ethereum tests path. Please provide a root path for BlockchainTests folder.')
        sys.exit(1)

    if len(sys.argv) >= 3:
        test_fork = sys.argv[2]


    test_dir = os.path.join(sys.argv[1] + "_" + test_fork, 'BlockchainTests')

    header = f'''"""DO NOT MODIFY: Tests generated from `{os.path.join(*folder.split('/')[-2:])}` with make_BlockchainTests.py"""
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
from manticore.core.state import TerminateState
from manticore.platforms import evm
from manticore.utils import config
from manticore.core.state import Concretize



class Log(rlp.Serializable):
    fields = [
        ('address', Binary.fixed_length(20, allow_empty=True)),
        ('topics', CountableList(BigEndianInt(32))),
        ('data', Binary())
    ]


class EVMTest_{os.path.splitext(os.path.basename(folder))[0]}(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None

    SAVED_DEFAULT_FORK = evm.DEFAULT_FORK

    @classmethod
    def setUpClass(cls):
        consts = config.get_group('evm')
        consts.oog = 'pedantic'
        evm.DEFAULT_FORK = '{DISASSEMBLE_FORK}'

    @classmethod
    def tearDownClass(cls):
        evm.DEFAULT_FORK = cls.SAVED_DEFAULT_FORK

    def _test_run(self, world):
        terminated = False
        result = None
        returndata = b''
        while world._pending_transaction is not None or world.depth > 0:
            assert not terminated
            try:
                world.execute()
            except Concretize as e:
                value = self._solve(world.constraints, e.expression)
                class fake_state:pass
                fake_state = fake_state()
                fake_state.platform = world
                e.setstate(fake_state, value)
            except TerminateState:
                terminated = True
        assert terminated
        return result, returndata

    def _solve(self, constraints, val):
        results = Z3Solver.instance().get_all_values(constraints, val, maxcnt=3)
        # We constrain all values to single values!
        self.assertEqual(len(results), 1)
        return results[0]

'''

    print(f"Generating tests from dir {folder}...", file=sys.stderr)
    cnt = 0

    for dirpath, dirnames, filenames in os.walk(folder):
        relpath = os.path.relpath(dirpath, folder)
        if not os.path.exists(os.path.join(test_dir, relpath)):
            os.makedirs(os.path.join(test_dir, relpath))

        for filename in filenames:
            if not filename.endswith(".json"):
                continue

            fp = open(os.path.join(dirpath, filename))
            testcase = dict(json.loads(fp.read()))
            fp.close()
            have_tests = False
            output = header
            for name, testcase in testcase.items():
                if test_fork not in name:
                    continue
                try:
                    output += (
                        gen_test(testcase, os.path.join(dirpath, filename), symbolic=symbolic)
                        + "\n"
                    )
                    cnt += 1
                except NotImplementedError as e:
                    print(f"{filename}: {name}: {e}", file=sys.stderr)
                    continue
                have_tests = True
                sys.stderr.write('.')
                sys.stderr.flush()

            if not have_tests:
                continue

            output += """

if __name__ == '__main__':
    unittest.main()
"""
            postfix = "symbolic" if symbolic else "concrete"
            with open(os.path.join(os.path.join(test_dir, relpath, filename[:-5] + "_" + postfix + ".py")), "w") as f:
                f.write(output)

    print(file=sys.stderr)
    print(f"Generated {cnt} testcases from jsons in {folder}.", file=sys.stderr)
