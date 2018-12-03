import subprocess
import sys
import time
import unittest

import os
import shutil
import tempfile

from manticore.binary import Elf, CGCElf
from manticore.utils.mappings import mmap, munmap

DIRPATH = os.path.dirname(__file__)

# Workaround for PyCharm's remote ssh interpreter that is in virtualenv
# (it doesn't support venv on remote ssh, so `python` may point to system's Python)
# and /proc/self/exe should always be the Python the tests have been run with.
PYTHON_BIN = '/proc/self/exe'


# TLDR: when we launch `python -m manticore` and one uses PyCharm remote interpreter
# the `python` might not refer to proper interpreter. The `/proc/self/exe` is a workaround
# so one doesn't have to set up virtualenv in a remote interpreter.
PYTHON_BIN = '/proc/self/exe'


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

    def _load_visited(self, visited):
        self.assertTrue(os.path.exists(visited))

        with open(visited, 'r') as f:
            vitems = f.read().splitlines()

        return [int(x[2:], 16) for x in vitems]

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

    @unittest.skip('Debug')
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
        t = time.time()

        with open(os.path.join(os.pardir, self.test_dir, 'output.log'), "w") as output:
            subprocess.check_call(['python', '-m', 'manticore',
                                '--workspace', workspace,
                                '--timeout', '1',
                                '--procs', '4',
                                filename,
                                '+++++++++'], stdout=output)

        output = subprocess.check_output([PYTHON_BIN, '-m', 'manticore',
                                          '--workspace', workspace,
                                          '--timeout', '1',
                                          '--procs', '4',
                                          '--no-color',
                                          filename,
                                          '+++++++++'])
        expected_output_regex = (
            b'.*m.manticore:INFO: Loading program .*tests/binaries/arguments_linux_amd64\n'
            b'.*m.manticore:INFO: Results in /tmp/[a-z0-9_]+/workspace\n'
            b'.*m.manticore:INFO: Total time: [0-9]+.[0-9]+\n'
        )

        self.assertRegex(output, expected_output_regex)

        self.assertTrue(time.time() - t < 20)

    @unittest.skip('Debug')
    def test_logger_verbosity(self):
        """
        Tests that default verbosity produces the expected volume of output
        """
        filename = os.path.join(DIRPATH, 'binaries', 'basic_linux_amd64')
        output = subprocess.check_output([PYTHON_BIN, '-m', 'manticore', '--no-color', filename])

        output_lines = output.splitlines()
        start_info = output_lines[:2]
        testcase_info = output_lines[2:-5]
        stop_info = output_lines[-5:]

        self.assertEqual(len(start_info), 2)
        self.assertEqual(len(stop_info), 5)

        for line in testcase_info:
            self.assertIn('Generated testcase', line)

    def _test_arguments_assertions_aux(self, binname, refname, testcases_number):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', binname))
        self.assertTrue(filename.startswith(os.getcwd()))

        filename = filename[len(os.getcwd()) + 1:]
        workspace = '%s/workspace' % self.test_dir
        assertions = '%s/assertions.txt' % self.test_dir

        with open(assertions, 'w') as f:
            f.write('0x0000000000401003 ZF == 1')

        cmd = [
            PYTHON_BIN, '-m', 'manticore',
            '--workspace', workspace,
            '--proc', '4',
            '--no-color',
            '--assertions', assertions,
            filename,
            '+++++++++',
        ]

        output = subprocess.check_output(cmd)

        expected_output_regex = b'.*m.manticore:INFO: Loading program .*binaries/%s\n' % bytes(binname, 'utf-8')

        expected_output_regex += b'.*m.manticore:INFO: Generated testcase No. [0-9][0-9]? -' \
                                 b' Program finished with exit status: [01]\n' * testcases_number

        expected_output_regex += b'.*m.manticore:INFO: Results in /tmp/[a-z0-9_]+/workspace\n'
        expected_output_regex += b'.*m.manticore:INFO: Total time: [0-9]+.[0-9]+\n'

        self.assertRegex(output, expected_output_regex)

        actual = self._load_visited(os.path.join(DIRPATH, workspace, 'visited.txt'))
        expected = self._load_visited(os.path.join(DIRPATH, 'reference', refname))

        self.assertEqual(actual, expected)

    @unittest.skip('Debug')
    def test_arguments_assertions_amd64(self):
        self._test_arguments_assertions_aux('arguments_linux_amd64', 'arguments_linux_amd64_visited.txt',
                                            testcases_number=1)

    def test_arguments_assertions_armv7(self):
        self._test_arguments_assertions_aux('arguments_linux_armv7', 'arguments_linux_armv7_visited.txt',
                                            testcases_number=19)

    @unittest.skip('Debug')
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

        actual = self._load_visited(os.path.join(DIRPATH, workspace, 'visited.txt'))
        self.assertTrue(len(actual) > 100)

    @unittest.skip('Debug')
    def test_eth_regressions(self):
        issues = [
            {'number': 676, 'contract': None, 'txlimit': 1},
            {'number': 678, 'contract': None, 'txlimit': 1},
            {'number': 701, 'contract': None, 'txlimit': 1},
            {'number': 714, 'contract': None, 'txlimit': 1},
            {'number': 735, 'contract': None, 'txlimit': 2},
            {'number': 760, 'contract': None, 'txlimit': 1},
            {'number': 780, 'contract': None, 'txlimit': 1},
            {'number': 795, 'contract': None, 'txlimit': 1},
            {'number': 799, 'contract': 'C', 'txlimit': 1},
            {'number': 807, 'contract': 'C', 'txlimit': 1},
            {'number': 808, 'contract': 'C', 'txlimit': 1},
            {'number': 'main/main', 'contract': 'C', 'txlimit': 1, 'in_directory': 'imports_issue'}
        ]

        for issue in issues:
            self._simple_cli_run(
                f'{issue["number"]}.sol', contract=issue['contract'], tx_limit=issue['txlimit'],
                in_directory=issue.get('in_directory')
            )

    @unittest.skip('Debug')
    def test_eth_705(self):
        # This test needs to run inside tests/binaries because the contract imports a file
        # that is in the tests/binaries dir
        old_cwd = os.getcwd()
        try:
            self._simple_cli_run('705.sol')
        finally:
            os.chdir(old_cwd)

    @unittest.skip('Debug')
    def test_basic_arm(self):
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries', 'basic_linux_armv7'))
        workspace = os.path.join(self.test_dir, 'workspace')

        output = subprocess.check_output([PYTHON_BIN, '-m', 'manticore', '--no-color', '--workspace', workspace, filename])

        expected_output_regex = (
            b'.*m.manticore:INFO: Loading program .*tests/binaries/basic_linux_armv7\n'
            b'.*m.manticore:INFO: Generated testcase No. 0 - Program finished with exit status: 0\n'
            b'.*m.manticore:INFO: Generated testcase No. 1 - Program finished with exit status: 0\n'
            b'.*m.manticore:INFO: Results in /tmp/[a-z0-9_]+/workspace\n'
            b'.*m.manticore:INFO: Total time: [0-9]+.[0-9]+\n'
        )

        self.assertRegex(output, expected_output_regex)

        with open(os.path.join(workspace, "test_00000000.stdout")) as f:
            self.assertIn("Message", f.read())
        with open(os.path.join(workspace, "test_00000001.stdout")) as f:
            self.assertIn("Message", f.read())

    @unittest.skip('Debug')
    def test_brk_regression(self):
        """
        Tests for brk behavior. Source of brk_static_amd64:

        #include <stdio.h>
        #include <unistd.h>
        #include <stdint.h>

        int main(int argc, char *argv[])
        {
            uint8_t *p = sbrk(0);

            int valid_at_first = (p == sbrk(16));
            int valid_after_shift = ((p+16) == sbrk(0));
            sbrk(-16);
            int valid_after_reset = (p == sbrk(0));
            sbrk(-(2<<20));
            int valid_after_bad_brk = (p == sbrk(0));

            if (valid_at_first && valid_after_shift
                && valid_after_reset && valid_after_bad_brk)
            return 0;
            else
            return 1;
        }
        """
        filename = os.path.abspath(os.path.join(DIRPATH, 'binaries/brk_static_amd64'))
        workspace = f'{self.test_dir}/workspace'

        output = subprocess.check_output([PYTHON_BIN, '-m', 'manticore', '--no-color', '--workspace', workspace, filename])

        expected_output_regex = (
            b'.*m.manticore:INFO: Loading program .+/tests/binaries/brk_static_amd64\n'
            b'.*m.manticore:INFO: Generated testcase No. 0 - Program finished with exit status: 0\n'
            b'.*m.manticore:INFO: Results in /tmp/[a-z0-9_]+/workspace\n'
            b'.*m.manticore:INFO: Total time: [0-9]+.[0-9]+\n'
        )

        self.assertRegex(output, expected_output_regex)

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
