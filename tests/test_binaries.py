import StringIO
import unittest
import sys
import shutil
import tempfile
import os
import hashlib
import subprocess
import time

#logging.basicConfig(filename = "test.log",
#                format = "%(asctime)s: %(name)s:%(levelname)s: %(message)s",
#                level = logging.DEBUG)

class IntegrationTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)

    def _loadVisitedSet(self, visited):

        self.assertTrue(os.path.exists(visited))
        vitems = open(visited, 'r').read().splitlines()

        vitems = map(lambda x: int(x[2:], 16), vitems)

        return set(vitems)

    def _simple_cli_run(self, filename):
        """
        Simply run the Manticore command line with `filename`
        :param filename: Name of file inside the `tests/binaries` directory
        :return:
        """
        dirname = os.path.dirname(__file__)
        filename = '{}/binaries/{}'.format(dirname, filename)
        subprocess.check_call(['python', '-m', 'manticore', filename], stdout=subprocess.PIPE)

    def _runWithTimeout(self, procargs, logfile, timeout=1200):

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

    def testTimeout(self):
        dirname = os.path.dirname(__file__)
        filename = os.path.abspath(os.path.join(dirname, 'binaries/arguments_linux_amd64'))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd())+1:]
        workspace = '%s/workspace'%self.test_dir
        t = time.time()
        with open(os.path.join(os.pardir, '%s/output.log'%self.test_dir), "w") as output:
            subprocess.check_call(['python', '-m', 'manticore',
                                '--workspace', workspace,
                                '--timeout', '1',
                                '--procs', '4',
                                filename,
                                '+++++++++'], stdout=output)

        self.assertTrue(time.time()-t < 20)

    def test_logger_verbosity(self):
        """
        Tests that default verbosity produces the expected volume of output
        """

        dirname = os.path.dirname(__file__)
        filename = os.path.join(dirname, 'binaries/basic_linux_amd64')
        output = subprocess.check_output(['python', '-m', 'manticore', filename])
        output_lines = output.splitlines()
        start_info = output_lines[:2]
        testcase_info = output_lines[2:-5]
        stop_info = output_lines[-5:]

        self.assertEqual(len(start_info), 2)
        self.assertEqual(len(stop_info), 5)

        for line in testcase_info:
            self.assertIn('Generated testcase', line)

    def testArgumentsAssertions(self):
        dirname = os.path.dirname(__file__)
        filename = os.path.abspath(os.path.join(dirname, 'binaries/arguments_linux_amd64'))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd())+1:]
        workspace = '%s/workspace'%self.test_dir
        assertions = '%s/assertions.txt'%self.test_dir
        file(assertions,'w').write('0x0000000000401003 ZF == 1')
        with open(os.path.join(os.pardir, '%s/output.log'%self.test_dir), "w") as output:
            subprocess.check_call(['python', '-m', 'manticore',
                                   '--workspace', workspace,
                                   '--proc', '4',
                                   '--assertions', assertions,
                                   filename,
                                   '+++++++++'], stdout=output)
        actual = self._loadVisitedSet(os.path.join(dirname, '%s/visited.txt'%workspace))
        expected = self._loadVisitedSet(os.path.join(dirname, 'reference/arguments_linux_amd64_visited.txt'))
        self.assertGreaterEqual(actual, expected)

    def testDecree(self):
        dirname = os.path.dirname(__file__)
        filename = os.path.abspath(os.path.join(dirname, 'binaries/cadet_decree_x86'))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd())+1:]
        workspace = '%s/workspace'%self.test_dir
        self._runWithTimeout(['python', '-m', 'manticore',
                    '--workspace', workspace,
                    '--timeout', '20',
                    '--proc', '4',
                    '--policy', 'uncovered',
                    filename], '%s/output.log'%self.test_dir)

        actual = self._loadVisitedSet(os.path.join(dirname, '%s/visited.txt'%workspace))
        self.assertTrue(len(actual) > 100 )

    def test_eth_regressions(self):
        contracts = [676, 678, 701, 714, 735, 760]
        for contract in contracts:
            self._simple_cli_run('{}.sol'.format(contract))

    def test_eth_705(self):
        # This test needs to run inside tests/binaries because the contract imports a file
        # that is in the tests/binaries dir
        dirname = os.path.dirname(__file__)
        old_cwd = os.getcwd()
        os.chdir('{}/binaries'.format(dirname))
        self._simple_cli_run('705.sol')
        os.chdir(old_cwd)

    def test_basic_arm(self):
        dirname = os.path.dirname(__file__)
        filename = os.path.abspath(os.path.join(dirname, 'binaries/basic_linux_armv7'))
        workspace = '%s/workspace' % self.test_dir
        output = subprocess.check_output(['python', '-m', 'manticore', '--workspace', workspace, filename])

        with open(os.path.join(workspace, "test_00000000.stdout")) as f:
            self.assertIn("Message", f.read())
        with open(os.path.join(workspace, "test_00000001.stdout")) as f:
            self.assertIn("Message", f.read())

if __name__ == '__main__':
    unittest.main()

