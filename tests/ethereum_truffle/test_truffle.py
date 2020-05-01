import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

from manticore.ethereum import ABI

DIRPATH = os.path.dirname(__file__)

# TLDR: when we launch `python -m manticore` and one uses PyCharm remote interpreter
# the `python` might not refer to proper interpreter. The `/proc/self/exe` is a workaround
# so one doesn't have to set up virtualenv in a remote interpreter.
PYTHON_BIN = sys.executable

# sam.moelius: All of these tests assume that an Ethereum node is listening on 127.0.0.1:7545.
URL = "127.0.0.1:7545"


class EthTruffleTests(unittest.TestCase):
    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)

    def test_bad_ip(self):
        workspace = os.path.join(self.test_dir, "workspace")

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--no-color",
            "--rpc",
            "127.0.0.2:7545",
            "--txtarget",
            "0x111111111111111111111111111111111111111",
        ]
        mcore = subprocess.Popen(cmd, stdout=subprocess.PIPE)

        # sam.moelius: Manticore should have failed to connect.
        self.assertRegex(
            mcore.stdout.read().decode(),
            r"\bm\.main:ERROR: \"Could not connect to 127.0.0.2:7545: Connect call failed \('127.0.0.2', 7545\)\"",
        )

        # sam.moelius: Wait for manticore to finish.
        self.assertEqual(mcore.wait(), 0)

    def test_bad_port(self):
        workspace = os.path.join(self.test_dir, "workspace")

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--no-color",
            "--rpc",
            "127.0.0.1:7546",
            "--txtarget",
            "0x111111111111111111111111111111111111111",
        ]
        mcore = subprocess.Popen(cmd, stdout=subprocess.PIPE)

        # sam.moelius: Manticore should have failed to connect.
        self.assertRegex(
            mcore.stdout.read().decode(),
            r"\bm\.main:ERROR: \"Could not connect to 127.0.0.1:7546: Connect call failed \('127.0.0.1', 7546\)\"",
        )

        # sam.moelius: Wait for manticore to finish.
        self.assertEqual(mcore.wait(), 0)

    def test_basic(self):
        dir = os.path.abspath(os.path.join(DIRPATH, "truffle", "basic"))
        workspace = os.path.join(self.test_dir, "workspace")

        os.chdir(dir)

        cmd = ["truffle", "deploy"]
        output = subprocess.check_output(cmd).decode()
        matches = [x for x in re.finditer(r"> contract address:\s*(0x\S*)", output)]
        self.assertEqual(len(matches), 2)
        address = matches[1].group(1)

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--no-color",
            "--rpc",
            URL,
            "--txtarget",
            address,
            "--txlimit",
            "1",
        ]
        subprocess.check_call(cmd)

        # sam.moelius: Manticore should have found a call to guess_x with the value of x, and a call
        # to guess_y with the value of y.
        cmd = [
            "grep",
            "-r",
            "--include=*.tx",
            "^Data: 0x"
            + ABI.function_selector("guess_x(uint256)").hex()
            + "%0.64x" % int.from_bytes("constructor".encode(), byteorder="big"),
            workspace,
        ]
        subprocess.check_call(cmd)

        cmd = [
            "grep",
            "-r",
            "--include=*.tx",
            "^Data: 0x"
            + ABI.function_selector("guess_y(uint256)").hex()
            + "%0.64x" % int.from_bytes("set_y".encode(), byteorder="big"),
            workspace,
        ]
        subprocess.check_call(cmd)

    # sam.moelius: test_predeployed is similar to test_basic. The difference is that
    # test_predeployed involves two contracts: one deployed by truffle, and one deployed
    # (internally) by Manticore.
    def test_predeployed(self):
        dir = os.path.abspath(os.path.join(DIRPATH, "truffle", "predeployed"))
        workspace = os.path.join(self.test_dir, "workspace")

        os.chdir(dir)

        cmd = ["truffle", "deploy"]
        output = subprocess.check_output(cmd).decode()
        matches = [x for x in re.finditer(r"> contract address:\s*(0x\S*)", output)]
        self.assertEqual(len(matches), 2)
        address = matches[1].group(1)

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--no-color",
            "--rpc",
            URL,
            "--txlimit",
            "1",
            "--contract",
            "Guesser",
            """
                interface Predeployed {
                    function x() external returns (uint256);
                    function y() external returns (uint256);
                }
                contract Guesser {
                    function guess_x(uint256 _x) external {
                        require(Predeployed(%s).x() == _x, "x != _x");
                    }
                    function guess_y(uint256 _y) external {
                        require(Predeployed(%s).y() == _y, "y != _y");
                    }
                }
            """ % (address, address),
        ]
        subprocess.check_call(cmd)

        # sam.moelius: Manticore should have found a call to guess_x with the value of x, and a call
        # to guess_y with the value of y.
        cmd = [
            "grep",
            "-r",
            "--include=*.tx",
            "^Data: 0x"
            + ABI.function_selector("guess_x(uint256)").hex()
            + "%0.64x" % int.from_bytes("constructor".encode(), byteorder="big"),
            workspace,
        ]
        subprocess.check_call(cmd)

        cmd = [
            "grep",
            "-r",
            "--include=*.tx",
            "^Data: 0x"
            + ABI.function_selector("guess_y(uint256)").hex()
            + "%0.64x" % int.from_bytes("set_y".encode(), byteorder="big"),
            workspace,
        ]
        subprocess.check_call(cmd)

    # sam.moelius: One purpose of test_maze is to give Manticore a lot of work, so that we can alter
    # the blockchain while it is working.
    def test_maze(self):
        dir = os.path.abspath(os.path.join(DIRPATH, "truffle", "maze"))
        workspace = os.path.join(self.test_dir, "workspace")

        os.chdir(dir)

        cmd = ["truffle", "deploy"]
        output = subprocess.check_output(cmd).decode()
        matches = [x for x in re.finditer(r"> contract address:\s*(0x\S*)", output)]
        self.assertEqual(len(matches), 2)
        address = matches[1].group(1)

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--no-color",
            "--rpc",
            URL,
            "--txtarget",
            address,
            "--txnocoverage",
        ]
        mcore = subprocess.Popen(cmd, stdout=subprocess.PIPE)

        # sam.moelius: Burn some ether just to alter the blockchain. It appears that truffle
        # console's stdin must be kept open, or else it will not do what you ask of it.
        cmd = ["truffle", "console"]
        truffle_console = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        truffle_console.stdin.write(
            b"web3.eth.getCoinbase().then(account => web3.eth.sendTransaction({"
            + b' to: "0x0000000000000000000000000000000000000000",'
            + b" from: account,"
            + b' value: web3.utils.toWei("10", "ether")'
            + b"}))\n"
        )
        truffle_console.stdin.flush()
        for line in truffle_console.stdout:
            if re.search(r"\btransactionHash\b", line.decode()):
                break
        truffle_console.stdin.close()

        # sam.moelius: Wait for truffle console to finish.
        self.assertEqual(mcore.wait(), 0)

        # sam.moelius: Wait for manticore to finish.
        self.assertEqual(mcore.wait(), 0)

        # sam.moelius: Manticore should have complained that the blockchain was altered.
        self.assertRegex(
            mcore.stdout.read().decode(),
            r"\bblocknumber has changed\b.*\bsomeone is using the endpoint besides us\b",
        )

        # sam.moelius: Manticore should have found a path through the maze.
        cmd = ["grep", "-r", "--include=*.logs", "You won!", workspace]
        subprocess.check_call(cmd)
