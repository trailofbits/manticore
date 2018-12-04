import subprocess
import sys
import time
import unittest

import os
import shutil
import tempfile

from manticore.binary import Elf, CGCElf
from manticore.native.mappings import mmap, munmap

DIRPATH = os.path.dirname(__file__)

# TLDR: when we launch `python -m manticore` and one uses PyCharm remote interpreter
# the `python` might not refer to proper interpreter. The `/proc/self/exe` is a workaround
# so one doesn't have to set up virtualenv in a remote interpreter.
PYTHON_BIN = sys.executable


class TestBinaryPackage(unittest.TestCase):
    _multiprocess_can_split_ = True

    def test_elf(self):
        filename = os.path.join(os.path.dirname(__file__), 'binaries', 'basic_linux_amd64')
        f = Elf(filename)
        self.assertTrue(
            [(4194304, 823262, 'r x', 'tests/binaries/basic_linux_amd64', 0, 823262),
             (7118520, 16112, 'rw ', 'tests/binaries/basic_linux_amd64', 827064, 7320)],
            list(f.maps())
        )
        self.assertTrue([('Running', {'EIP': 4196624})], list(f.threads()))
        self.assertIsNone(f.getInterpreter())
        f.elf.stream.close()

    def test_decree(self):
        filename = os.path.join(os.path.dirname(__file__), 'binaries', 'cadet_decree_x86')
        f = CGCElf(filename)
        self.assertTrue(
            [(134512640, 1478, 'r x', 'tests/binaries/cadet_decree_x86', 0, 1478)],
            list(f.maps())
        )
        self.assertTrue([('Running', {'EIP': 134513708})], list(f.threads()))
        f.elf.stream.close()


class IntegrationTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)

    def _load_visited_set(self, visited):
        self.assertTrue(os.path.exists(visited))

        with open(visited, 'r') as f:
            vitems = f.read().splitlines()

        return set(int(x[2:], 16) for x in vitems)

    def _simple_cli_run(self, filename, contract=None, tx_limit=1, in_directory=None):
        """
        Simply run the Manticore command line with `filename`
        :param filename: Name of file inside the `tests/binaries` directory
        :return:
        """
        working_dir = os.path.join(DIRPATH, 'binaries')

        if in_directory:
            working_dir = os.path.join(working_dir, in_directory)

        command = [PYTHON_BIN, '-m', 'manticore']

        if contract:
            command.append('--contract')
            command.append(contract)
        command.append('--txlimit')
        command.append(str(tx_limit))
        command.append('--no-testcases')
        command.append(filename)

        subprocess.check_call(command, stdout=subprocess.PIPE, cwd=working_dir)

    def _run_with_timeout(self, procargs, logfile, timeout=1200):

        with open(os.path.join(os.pardir, logfile), "w") as output:
            po = subprocess.Popen(procargs, stdout=output)
            secs_used = 0

            while po.poll() is None and secs_used < timeout:
                time.sleep(1)
                sys.stderr.write("~")
                secs_used += 1

            self.assertEqual(po.returncode, 0)
            self.assertTrue(secs_used < timeout)
            sys.stderr.write("\n")

    def test_timeout(self):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', 'arguments_linux_amd64'))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd()) + 1:]
        workspace = os.path.join(self.test_dir, 'workspace')
        t = time.time()
        with open(os.path.join(os.pardir, self.test_dir, 'output.log'), "w") as output:
            subprocess.check_call([PYTHON_BIN, '-m', 'manticore',
                                '--workspace', workspace,
                                '--timeout', '1',
                                '--procs', '4',
                                filename,
                                '+++++++++'], stdout=output)

        self.assertTrue(time.time()-t < 20)

    def test_solidity_timeout(self):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', 'int_overflow.sol'))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd())+1:]
        workspace = os.path.join(self.test_dir, 'workspace')

        timeout_secs = 1

        cmd = [
            PYTHON_BIN, '-m', 'manticore',
            '--workspace', workspace,
            '--timeout', str(timeout_secs),
            '--no-color',
            filename,
            '+++++++++'
        ]

        start = time.time()
        output = subprocess.check_output(cmd)
        end = time.time()

        output = output.splitlines()

        self.assertEqual(len(output), 1)
        self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])

        # Since we count the total time of Python process that runs Manticore, it takes a bit more time
        # than the timeout value, so we just assert two seconds here (1.5s should also be fine)
        self.assertLessEqual(end - start, timeout_secs+1)

    def test_logger_verbosity(self):
        """
        Tests that default verbosity produces the expected volume of output
        """
        filename = os.path.join(DIRPATH, 'binaries', 'basic_linux_amd64')
        output = subprocess.check_output([PYTHON_BIN, '-m', 'manticore', '--no-color', filename])

        output_lines = output.splitlines()

        self.assertEqual(len(output_lines), 6)

        self.assertIn(b'Verbosity set to 1.', output_lines[0])
        self.assertIn(b'Loading program', output_lines[1])
        self.assertIn(b'Generated testcase No. 0 - Program finished with exit status: 0', output_lines[2])
        self.assertIn(b'Generated testcase No. 1 - Program finished with exit status: 0', output_lines[3])
        self.assertIn(b'Results in ', output_lines[4])
        self.assertIn(b'Total time: ', output_lines[5])

    def _test_arguments_assertions_aux(self, binname, testcases_number, visited, add_assertion=False):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', binname))

        self.assertTrue(filename.startswith(os.getcwd()))

        filename = filename[len(os.getcwd()) + 1:]
        workspace = '%s/workspace' % self.test_dir

        cmd = [
            PYTHON_BIN, '-m', 'manticore',
            '--workspace', workspace,
            '--proc', '4',
            '--no-color',
        ]

        # Only for amd64 binary/case
        if add_assertion:
            assertions = '%s/assertions.txt' % self.test_dir

            with open(assertions, 'w') as f:
                f.write('0x0000000000401003 ZF == 1')

            cmd += ['--assertions', assertions]

        cmd += [
            filename,
            '+++++++++',
        ]

        output = subprocess.check_output(cmd).splitlines()

        self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])

        self.assertIn(b'm.n.manticore:INFO: Loading program', output[1])
        self.assertIn(bytes(binname, 'utf-8'), output[1])  # the binname should be in the path

        for i in range(testcases_number):
            line = output[2+i]

            # After `expected1` there's the testcase id; because we fork use `--proc 4`
            # it might not be in the increasing order
            expected1 = b'm.c.manticore:INFO: Generated testcase No. '
            expected2 = b'- Program finished with exit status: '

            self.assertIn(expected1, line)
            self.assertIn(expected2, line)

        self.assertIn(b'm.c.manticore:INFO: Results in /tmp', output[2+testcases_number])
        self.assertIn(b'm.c.manticore:INFO: Total time: ', output[2+testcases_number+1])

        actual = self._load_visited_set(os.path.join(DIRPATH, workspace, 'visited.txt'))

        self.assertLess(set(visited), actual)

        # this differs locally and on travis, but it is a good value that works on both...
        self.assertGreater(len(actual), 2000)

        self.assertEqual(len(set(visited)), len(visited))  # just a sanity check

    def test_arguments_assertions_amd64(self):
        self._test_arguments_assertions_aux('arguments_linux_amd64', testcases_number=1, visited=[
            0x00400e40,  # _start
            0x00400e64,  # call in _start
            0x00401040,  # called function (let's name it A)
            0x00401087,  # branch (je instruction)
            0x004011c2,  # je taken
            0x00401096,  # branches merge here
            0x004010ca,  # end of the block,
            0x004010d0,  # next block
            0x004010db,  # `call B` instruction
            0x004369b0,  # called function [has switch], let's name it B

            # Switch cases in B:
            #      0xa,        0x9,        0x2,        0x0,        0x8,        0x3,
            0x00436a20, 0x00436a30, 0x00436a40, 0x00436a50, 0x00436a60, 0x00436a70,
            #      0xe,        0xd,        0xb,       0x16,
            0x00436aa0, 0x00436ab8, 0x00436ad0, 0x00436ae0,

            0x00436b57,  # ret in B

            0x00401148,  # A should eventually branch and get to this branch
            0x004012c5,  # end of A

            0x004002d8,  # _init
            0x004002f1,  # ret in _init
            0x0049124c,  # _fini
            0x00491254,  # ret in _fini
        ], add_assertion=True)

    def test_arguments_assertions_armv7(self):
        self._test_arguments_assertions_aux('arguments_linux_armv7', testcases_number=19, visited=[
            0x00008b98,  # _start
            0x00008bc0,  # bl __libc_start_main
            0x00008d0c,  # main

            0x00008d3c,  # branch not taken in main
            0x00008d60,  # another branch, when --dostuff is passed
            0x00008d70,  # dont do anything block
            0x00008d7c,  # next block

            0x0001d28c,  # return from strcmp

            0x00008f88,  # exit from libc start main

            0x00008158,  # _init
            0x00008160,  # end of _init

            0x00008b88,  # fini
            0x00008b90,  # end of fini
        ])

    def test_decree(self):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', 'cadet_decree_x86'))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd()) + 1:]
        workspace = os.path.join(self.test_dir, 'workspace')
        self._run_with_timeout([PYTHON_BIN, '-m', 'manticore',
                              '--workspace', workspace,
                              '--timeout', '20',
                              '--proc', '4',
                              '--no-color',
                              '--policy', 'uncovered',
                                filename], os.path.join(self.test_dir, 'output.log'))

        actual = self._load_visited_set(os.path.join(DIRPATH, workspace, 'visited.txt'))
        self.assertTrue(len(actual) > 100)

    def test_eth_regressions_676(self):
        issue = {'number': 676, 'contract': None, 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_678(self):
        issue = {'number': 678, 'contract': None, 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_701(self):
        issue = {'number': 701, 'contract': None, 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_714(self):
        issue = {'number': 714, 'contract': None, 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_735(self):
        issue = {'number': 735, 'contract': None, 'txlimit': 2}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_760(self):
        issue = {'number': 760, 'contract': None, 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_780(self):
        issue = {'number': 780, 'contract': None, 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_795(self):
        issue = {'number': 795, 'contract': None, 'txlimit': 1}

        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_799(self):
        issue = {'number': 799, 'contract': 'C', 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_807(self):
        issue = {'number': 807, 'contract': 'C', 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_80(self):
        issue = {'number': 808, 'contract': 'C', 'txlimit': 1}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_regressions_mainmain(self):
        issue = {'number': 'main/main', 'contract': 'C', 'txlimit': 1, 'in_directory': 'imports_issue'}
        self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    def test_eth_705(self):
        # This test needs to run inside tests/binaries because the contract imports a file
        # that is in the tests/binaries dir
        old_cwd = os.getcwd()
        try:
            self._simple_cli_run('705.sol')
        finally:
            os.chdir(old_cwd)

    def test_basic_arm(self):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', 'basic_linux_armv7'))
        workspace = os.path.join(self.test_dir, 'workspace')
        cmd = [PYTHON_BIN, '-m', 'manticore', '--no-color', '--workspace', workspace, filename]

        output = subprocess.check_output(cmd).splitlines()

        self.assertEqual(len(output), 6)

        self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])
        self.assertIn(b'm.n.manticore:INFO: Loading program ', output[1])

        self.assertIn(b'm.c.manticore:INFO: Generated testcase No.', output[2])
        self.assertIn(b'- Program finished with exit status: 0', output[2])

        self.assertIn(b'm.c.manticore:INFO: Generated testcase No.', output[3])
        self.assertIn(b'- Program finished with exit status: 0', output[3])

        self.assertIn(b'm.c.manticore:INFO: Results in ', output[4])
        self.assertIn(b'm.c.manticore:INFO: Total time: ', output[5])

        with open(os.path.join(workspace, "test_00000000.stdout")) as f:
            self.assertIn("Message", f.read())
        with open(os.path.join(workspace, "test_00000001.stdout")) as f:
            self.assertIn("Message", f.read())

    def test_brk_regression(self):
        """
        Tests for brk behavior. Source of brk_static_amd64:

        #include <stdio.h>
        #include <unistd.h>
        #include <stdint.h>

        int main(int argc, char *argv[]) {
            uint8_t *p = sbrk(0);

            int valid_at_first = (p == sbrk(16));
            int valid_after_shift = ((p+16) == sbrk(0));
            sbrk(-16);
            int valid_after_reset = (p == sbrk(0));
            sbrk(-(2<<20));
            int valid_after_bad_brk = (p == sbrk(0));

            if (valid_at_first && valid_after_shift && valid_after_reset && valid_after_bad_brk)
                return 0;
            else
                return 1;
        }
        """
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries/brk_static_amd64'))
        workspace = f'{self.test_dir}/workspace'
        cmd = [PYTHON_BIN, '-m', 'manticore', '--no-color', '--workspace', workspace, filename]

        output = subprocess.check_output(cmd).splitlines()

        self.assertEqual(len(output), 5)

        self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])
        self.assertIn(b'm.n.manticore:INFO: Loading program ', output[1])
        self.assertIn(b'm.c.manticore:INFO: Generated testcase No. 0 - Program finished with exit status: 0', output[2])
        self.assertIn(b'm.c.manticore:INFO: Results in ', output[3])
        self.assertIn(b'm.c.manticore:INFO: Total time: ', output[4])

        with open(os.path.join(workspace, "test_00000000.messages")) as f:
            self.assertIn("finished with exit status: 0", f.read())

    def test_unaligned_mappings(self):
        # This test ensures that mapping file contents at non page-aligned offsets is possible.
        filename = os.path.join(os.path.dirname(__file__), 'binaries', 'basic_linux_amd64')
        with open(filename, 'rb') as f:
            for addr, size in [
                (0x0001, 0xfffe), (0x0001, 0x0fff), (0x0001, 0x1000),
                (0x0fff, 0x0001), (0x0fff, 0x0002), (0x0fff, 0x1000),
            ]:
                # No assert should be triggered on the following line
                munmap(mmap(f.fileno(), addr, size), size)


if __name__ == '__main__':
    unittest.main()
