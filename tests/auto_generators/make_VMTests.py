"""
This script generates VMTests that are used to check EVM's Istanbul fork correctness.

### TO GENERATE ALL:

## Initialize env:
cd manticore/tests/ && mkdir -p  ethereum_vm/VMTests_concrete 
git clone https://github.com/ethereum/tests --depth=1

## Get help
python make_VMTest.py --help 

## Generate concrete tests:
for i in  tests/BlockchainTests/ValidBlocks/VMTests/*/*json; do python make_VMTest.py -i $i --fork Istanbul -o ethereum_vm/VMTests_concrete; done

"""
import argparse
import sys
import logging
import os
import json
import pyevmasm as EVMAsm
from binascii import unhexlify


total_count = 0
DEFAULT_FORK = "Istanbul"

real_open = open


def fake_open(filename, mode="r", *args, **kwargs):
    """ Replace normal global open with this for a wuick dry run """
    from io import StringIO

    logging.info("Fake openning %r", (filename, mode) + args)
    if os.path.exists(filename):
        return StringIO(real_open(filename, "r").read())
    return StringIO()


def get_caller(nonce, price, gas, address, value, calldata, v, r, s):
    if address is None:
        to = b""
    else:
        to = unhexlify("%040x" % address)
    # pip install py-evm
    from eth.vm.forks.frontier.transactions import FrontierTransaction

    t = FrontierTransaction(
        nonce=nonce,
        gas_price=price,
        gas=gas,
        to=to,  # Can be the empty string.
        value=value,
        data=calldata,
        v=v,
        r=r,
        s=s,
    )
    return int.from_bytes(t.sender, "big")


def gen_header(testcases):
    header = f'''"""DO NOT MODIFY: Tests generated from `tests/` with {sys.argv[0]}"""
import unittest
from binascii import unhexlify
from manticore import ManticoreEVM, Plugin
from manticore.utils import config
'''

    if any("logs" in testcase for testcase in testcases.values()):
        body += """
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
"""

    header += """consts = config.get_group('core')
consts.mprocessing = consts.mprocessing.single
consts = config.get_group('evm')
consts.oog = 'pedantic'

class EVMTest(unittest.TestCase):
    # https://nose.readthedocs.io/en/latest/doc_tests/test_multiprocess/multiprocess.html#controlling-distribution
    _multiprocess_can_split_ = True
    # https://docs.python.org/3.7/library/unittest.html#unittest.TestCase.maxDiff
    maxDiff = None

"""
    return header


def gen_footer(testcase):
    footer = """

if __name__ == '__main__':
    unittest.main()"""
    return footer


def gen_body(name, testcase):
    body = f'''
    def test_{name}(self):
        """
        Testcase taken from https://github.com/ethereum/tests
        Source: {testcase['_info']['source']} 
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

'''
    for address, account in testcase["pre"].items():
        account_address = int(address, 0)
        account_code = account["code"][2:]
        account_nonce = int(account["nonce"], 0)
        account_balance = int(account["balance"], 0)

        disassembly = EVMAsm.disassemble(unhexlify(account_code), fork=DEFAULT_FORK.lower())
        disassembly = (
            '\n        """'
            + "\n            "
            + "\n            ".join(disassembly.split("\n"))
            + '\n        """'
        )
        body += f"""
        {disassembly if account_code else ''}
        m.create_account(address={hex(account_address)},
                         balance={account_balance}, 
                         code={"unhexlify('"+account_code+"')" if account_code else "b''"}, 
                         nonce={account_nonce})"""

        if "storage" in account and account["storage"]:
            body += """
        for state in m.all_states:
            world = state.platform"""

        for key, value in account["storage"].items():
            body += f"""
            world.set_storage_data({hex(account_address)}, {key}, {value})"""

    coinbases = set()
    for block in testcase["blocks"]:
        blockheader = block["blockHeader"]
        coinbases.add(blockheader["coinbase"])
    for coinbase in coinbases:
        body += f"""
        #coinbase
        m.create_account(address={coinbase},
                         balance=0, 
                         code=b'', 
                         nonce=0)
        """

    for block in testcase["blocks"]:
        blockheader = block["blockHeader"]

        body += f"""
        # Start a block
        self.assertEqual(m.count_all_states(), 1)
        m.start_block(blocknumber={blockheader['number']},
                      timestamp={blockheader['timestamp']},
                      difficulty={blockheader['difficulty']},
                      coinbase={blockheader['coinbase']},
                      gaslimit={hex(int(blockheader['gasLimit'],0))})

        #VMtest Transaction
"""

        for transaction in block["transactions"]:
            address = None if transaction["to"] == "" else int(transaction["to"], 16)
            calldata = unhexlify(transaction["data"][2:])
            gas = int(transaction["gasLimit"], 0)
            price = int(transaction["gasPrice"], 0)
            nonce = int(transaction["nonce"], 0)
            value = 0 if transaction["value"] == "0x" else int(transaction["value"], 0)
            r = int(transaction["r"], 0)
            s = int(transaction["s"], 0)
            v = int(transaction["v"], 0)
            caller = get_caller(nonce, price, gas, address, value, calldata, v, r, s)
            body += f"""

        m.transaction(caller={hex(caller)},
                      address={hex(address)},
                      value={value},
                      data={calldata},
                      gas={gas},
                      price={price})"""

    body += f"""
        for state in m.all_states:
            world = state.platform
            self.assertEqual(used_gas_plugin.used_gas, {blockheader['gasUsed']})
            
            world.end_block()"""

    for account_address, account in testcase["postState"].items():
        body += f"""
            # Add post checks for account {account_address}
            # check nonce, balance, code and storage values
            self.assertEqual(world.get_nonce({account_address}), {account['nonce']})
            self.assertEqual(world.get_balance({account_address}), {account['balance']})
            self.assertEqual(world.get_code({account_address}), {"unhexlify('"+account['code'][2:]+"')" if account['code'][2:] else "b''"})"""

        if account["storage"]:
            body += """
            # check storage"""

            for key, value in account["storage"].items():
                body += f"""
            self.assertEqual(world.get_storage_data({account_address}, {key}), {value})"""

    if "logs" in testcase:
        print(testcase["logs"])
        body += f"""
            # check logs
            logs = [Log(unhexlify('{'{'}:040x{'}'}'.format(l.address)), l.topics, solve(l.memlog)) for l in world.logs]
            data = rlp.encode(logs)
            self.assertEqual(sha3.keccak_256(data).hexdigest(), '{testcase['logs'][2:]}')"""

    return body


def gen_testfile(testcases, fork):
    global total_count
    output = gen_header(testcases)
    for name, testcase in testcases.items():
        if testcase["network"] != fork:
            logging.warning(
                f"Skipping testcase {name}. Wrong fork: {testcase['network']} != {fork}"
            )
            continue
        total_count += 1
        output += gen_body(name.replace("-", "_"), testcase)
    output += gen_footer(testcases)
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Manticore test generator for Ethereum BlockchainTests"
    )
    parser.add_argument(
        "-v", action="count", default=0, help="Specify verbosity level from -v to -vvvv"
    )
    parser.add_argument(
        "-f",
        "--fork",
        "--flavor",
        default=DEFAULT_FORK,
        type=str,
        help="Fork, default: byzantium. Possible: Byzantium, Constantinople, EIP150, EIP158, Frontier, Homestead, Istanbul."
        "Also an unsigned block number is accepted to select the fork.",
    )

    parser.add_argument(
        "-d", "--dry-run", default=False, action="store_true", help="Do not generate any file"
    )

    parser.add_argument(
        "-i", "--input-path", nargs="?", help="Path to Ethereum tests", required=True
    )
    parser.add_argument("-r", "--filter-regex", type=str, help="Filter by regex")
    parser.add_argument(
        "-o",
        "--output-path",
        nargs="?",
        default="!inplace",
        help="Output path, by default this generates a .py file in the same folder as the json input",
    )
    parser.add_argument(
        "-x", "--force", default=False, action="store_true", help="Overwrite any existing file"
    )
    args = parser.parse_args(sys.argv[1:])

    # logging
    loglevel = (logging.CRITICAL, logging.ERROR, logging.INFO, logging.DEBUG)
    logging.basicConfig(level=loglevel[min(args.v, 3)], format="%(message)s")

    # Forks
    accepted_forks = [
        "Byzantium",
        "Constantinople",
        "EIP150",
        "EIP158",
        "Frontier",
        "Homestead",
        "Istanbul",
    ]
    args.fork = args.fork.title()

    if args.fork not in accepted_forks:
        logging.error("Wrong fork name. Please provide one of %s.\n" % accepted_forks)
        sys.exit(1)

    # Dry run
    if args.dry_run:
        open = fake_open

    # input path
    if not os.path.isfile(args.input_path):
        logging.error("Wrong json test file (%s). Please provide one.\n" % args.input_path)
        sys.exit(1)

    with open(args.input_path) as fp:
        if not os.path.isfile(args.input_path) or not args.input_path.endswith(".json"):
            logging.debug("Input file args.input_path looks odd. Expecting a .json file.")
        testcases = dict(json.loads(fp.read()))

    logging.info(f"Loaded {len(testcases)} testcases from {args.input_path}")

    # output path
    if args.output_path == "!inplace":
        # /xxx/yyy/testfile.json -> ./testfile.py
        stem, ext = os.path.splitext(args.input_path)
        args.output_path = stem + ".py"
    elif os.path.isdir(args.output_path):
        # /xxx/yyy/testfile.json -> $output_path/yyy_testfile.py
        stem, ext = os.path.splitext(os.path.basename(args.input_path))
        output_path = os.path.join(args.output_path, f"test_{stem}.py")
        # If output pats collides add the containing folder to the name
        if os.path.exists(output_path):
            folders = args.input_path.split(os.sep)
            if len(folders) >= 2:
                output_path = os.path.join(args.output_path, f"test_{folders[-2]}_{stem}.py")
        args.output_path = output_path
    # or else /xxx/yyy/testfile.json -> $whatever

    if os.path.exists(args.output_path):
        if not args.force:
            logging.error(f"File {args.output_path} already exists. Consider adding --force")
            if not args.dry_run:
                sys.exit(1)
            logging.error(f"Continuing because it is a dry run. ")
        else:
            logging.info(f"File {args.output_path} already exists. Overwritting.")

    with open(args.output_path, "w") as fp:
        fp.write(gen_testfile(testcases, args.fork))

    logging.info(f"{total_count} unittests generated in {args.output_path}")
