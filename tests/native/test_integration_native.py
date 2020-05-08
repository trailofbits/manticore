import subprocess
import sys
import time
import unittest

import os
import shutil
import tempfile

from manticore.binary import Elf, CGCElf
from manticore.native.mappings import mmap, munmap

from typing import List, Set


DIRPATH: str = os.path.dirname(__file__)

PYTHON_BIN: str = sys.executable


class NativeIntegrationTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self) -> None:
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self) -> None:
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)

    def _load_visited_set(self, visited: str) -> Set[int]:
        self.assertTrue(os.path.exists(visited))

        with open(visited, "r") as f:
            vitems = f.read().splitlines()

        return set(int(x[2:], 16) for x in vitems)

    def _run_with_timeout(self, procargs: List[str], logfile: str, timeout: int = 1200) -> None:

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

    def test_timeout(self) -> None:
        filename = os.path.abspath(os.path.join(DIRPATH, "binaries", "arguments_linux_amd64"))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd()) + 1 :]
        workspace = os.path.join(self.test_dir, "workspace")
        t = time.time()
        with open(os.path.join(os.pardir, self.test_dir, "output.log"), "w") as output:
            subprocess.check_call(
                [
                    "coverage",
                    "run",  # PYTHON_BIN,
                    "-m",
                    "manticore",
                    "--workspace",
                    workspace,
                    "--core.timeout",
                    "1",
                    "--core.procs",
                    "4",
                    filename,
                    "+++++++++",
                ],
                stdout=output,
            )

        self.assertTrue(time.time() - t < 20)

    def test_logger_verbosity(self) -> None:
        """
        Tests that default verbosity produces the expected volume of output
        """
        filename = os.path.join(DIRPATH, "binaries", "basic_linux_amd64")
        workspace = os.path.join(self.test_dir, "workspace")
        output = subprocess.check_output(
            [PYTHON_BIN, "-m", "manticore", "--no-color", "--workspace", workspace, filename]
        )

        output_lines = output.splitlines()

        self.assertEqual(len(output_lines), 5)

        # self.assertIn(b'Verbosity set to 1.', output_lines[1])
        self.assertIn(b"Loading program", output_lines[0])
        self.assertIn(b"Generated testcase No. 0 -", output_lines[1])
        self.assertIn(b"Generated testcase No. 1 -", output_lines[2])

    def _test_arguments_assertions_aux(
        self, binname: str, testcases_number: int, visited: List[int], add_assertion: bool = False
    ) -> None:
        filename = os.path.abspath(os.path.join(DIRPATH, "binaries", binname))

        self.assertTrue(filename.startswith(os.getcwd()))

        filename = filename[len(os.getcwd()) + 1 :]
        workspace = "%s/workspace" % self.test_dir

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--workspace",
            workspace,
            "--core.procs",
            "4",
            "--no-color",
        ]

        # Only for amd64 binary/case
        if add_assertion:
            assertions = "%s/assertions.txt" % self.test_dir

            with open(assertions, "w") as f:
                f.write("0x0000000000401003 ZF == 1")

            cmd += ["--assertions", assertions]

        cmd += [filename, "+++++++++"]
        output = subprocess.check_output(cmd).splitlines()
        # self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])

        self.assertIn(b"m.n.manticore:INFO: Loading program", output[0])
        self.assertIn(bytes(binname, "utf-8"), output[0])  # the binname should be in the path

        for i in range(testcases_number):
            line = output[1 + i]

            # After `expected1` there's the testcase id; because we fork use `--core.procs 4`
            # it might not be in the increasing order
            expected1 = b"m.c.manticore:INFO: Generated testcase No. "
            # expected2 = b'- Program finished with exit status: '

            self.assertIn(expected1, line)
            # self.assertIn(expected2, line)

        # self.assertIn(b'm.c.manticore:INFO: Results in /tmp', output[2+testcases_number])
        # self.assertIn(b'm.c.manticore:INFO: Total time: ', output[2+testcases_number+1])

        actual = self._load_visited_set(os.path.join(DIRPATH, workspace, "visited.txt"))

        self.assertLess(set(visited), actual)

        # this differs locally and on travis, but it is a good value that works on both...
        self.assertGreater(len(actual), 2000)

        self.assertEqual(len(set(visited)), len(visited))  # just a sanity check

    def test_arguments_assertions_amd64(self) -> None:
        self._test_arguments_assertions_aux(
            "arguments_linux_amd64",
            testcases_number=1,
            visited=[
                0x00400E40,  # _start
                0x00400E64,  # call in _start
                0x00401040,  # called function (let's name it A)
                0x00401087,  # branch (je instruction)
                0x004011C2,  # je taken
                0x00401096,  # branches merge here
                0x004010CA,  # end of the block,
                0x004010D0,  # next block
                0x004010DB,  # `call B` instruction
                0x004369B0,  # called function [has switch], let's name it B
                # Switch cases in B:
                #      0xa,        0x9,        0x2,        0x0,        0x8,        0x3,
                0x00436A20,
                0x00436A30,
                0x00436A40,
                0x00436A50,
                0x00436A60,
                0x00436A70,
                #      0xe,        0xd,        0xb,       0x16,
                0x00436AA0,
                0x00436AB8,
                0x00436AD0,
                0x00436AE0,
                0x00436B57,  # ret in B
                0x00401148,  # A should eventually branch and get to this branch
                0x004012C5,  # end of A
                0x004002D8,  # _init
                0x004002F1,  # ret in _init
                0x0049124C,  # _fini
                0x00491254,  # ret in _fini
            ],
            add_assertion=True,
        )

    def test_arguments_assertions_armv7(self) -> None:
        self._test_arguments_assertions_aux(
            "arguments_linux_armv7",
            testcases_number=19,
            visited=[
                0x00008B98,  # _start
                0x00008BC0,  # bl __libc_start_main
                0x00008D0C,  # main
                0x00008D3C,  # branch not taken in main
                0x00008D60,  # another branch, when --dostuff is passed
                0x00008D70,  # dont do anything block
                0x00008D7C,  # next block
                0x0001D28C,  # return from strcmp
                0x00008F88,  # exit from libc start main
                0x00008158,  # _init
                0x00008160,  # end of _init
                0x00008B88,  # fini
                0x00008B90,  # end of fini
            ],
        )

    def test_decree(self) -> None:
        filename = os.path.abspath(os.path.join(DIRPATH, "binaries", "cadet_decree_x86"))
        self.assertTrue(filename.startswith(os.getcwd()))
        filename = filename[len(os.getcwd()) + 1 :]
        workspace = os.path.join(self.test_dir, "workspace")
        self._run_with_timeout(
            [
                PYTHON_BIN,
                "-m",
                "manticore",
                "--workspace",
                workspace,
                "--core.timeout",
                "20",
                "--core.procs",
                "4",
                "--no-color",
                "--policy",
                "uncovered",
                filename,
            ],
            os.path.join(self.test_dir, "output.log"),
        )

        actual = self._load_visited_set(os.path.join(DIRPATH, workspace, "visited.txt"))
        self.assertTrue(len(actual) > 100)

    def test_basic_arm(self) -> None:
        filename = os.path.abspath(os.path.join(DIRPATH, "binaries", "basic_linux_armv7"))
        workspace = os.path.join(self.test_dir, "workspace")
        cmd = [PYTHON_BIN, "-m", "manticore", "--no-color", "--workspace", workspace, filename]

        output = subprocess.check_output(cmd).splitlines()

        self.assertEqual(len(output), 5)
        # self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])
        self.assertIn(b"m.n.manticore:INFO: Loading program ", output[0])
        self.assertIn(b"m.c.manticore:INFO: Generated testcase No. 0 - ", output[1])
        self.assertIn(b"m.c.manticore:INFO: Generated testcase No. 1 - ", output[2])

        with open(os.path.join(workspace, "test_00000000.stdout")) as f:
            self.assertIn("Message", f.read())
        with open(os.path.join(workspace, "test_00000001.stdout")) as f:
            self.assertIn("Message", f.read())

    def _test_no_crash(self, test_name: str, *args) -> None:
        """
        Tests that the specified test binary doesn't cause Manticore to crash.
        """
        filename = os.path.abspath(os.path.join(DIRPATH, "binaries", test_name))
        workspace = os.path.join(self.test_dir, "workspace")
        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "--no-color",
            "--workspace",
            workspace,
            filename,
        ]
        cmd.extend(args)
        subprocess.check_call(cmd)

    def test_fclose_linux_amd64(self) -> None:
        """
        Tests that the `fclose` example for amd64 linux doesn't crash; see #1602 and #1604.
        """
        self._test_no_crash("fclose_linux_amd64", "+++++++")

    def test_fileio_linux_amd64(self) -> None:
        """
        Tests that the `fileio` example for amd64 linux doesn't crash.
        """
        self._test_no_crash("fileio_linux_amd64", "+")

    def test_ioctl_bogus(self) -> None:
        """
        Tests that the `ioctl_bogus_linux_amd64` example for amd64 linux doesn't crash.
        """
        self._test_no_crash("ioctl_bogus_linux_amd64")

    def test_ioctl_socket(self) -> None:
        """
        Tests that the `ioctl_socket_linux_amd64` example for amd64 linux doesn't crash.
        """
        self._test_no_crash("ioctl_socket_linux_amd64")

    def test_brk_regression(self) -> None:
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
        filename = os.path.abspath(os.path.join(DIRPATH, "binaries/brk_static_amd64"))
        workspace = f"{self.test_dir}/workspace"
        cmd = [PYTHON_BIN, "-m", "manticore", "--no-color", "--workspace", workspace, filename]

        output = subprocess.check_output(cmd).splitlines()

        self.assertEqual(len(output), 4)

        # self.assertIn(b'm.c.manticore:INFO: Verbosity set to 1.', output[0])
        self.assertIn(b"m.n.manticore:INFO: Loading program ", output[0])
        self.assertIn(b"m.c.manticore:INFO: Generated testcase No. 0 - ", output[1])

        # with open(os.path.join(workspace, "test_00000000.messages")) as f:
        #     self.assertIn("finished with exit status: 0", f.read())

    def test_unaligned_mappings(self) -> None:
        # This test ensures that mapping file contents at non page-aligned offsets is possible.
        filename = os.path.join(os.path.dirname(__file__), "binaries", "basic_linux_amd64")
        with open(filename, "rb") as f:
            for addr, size in [
                (0x0001, 0xFFFE),
                (0x0001, 0x0FFF),
                (0x0001, 0x1000),
                (0x0FFF, 0x0001),
                (0x0FFF, 0x0002),
                (0x0FFF, 0x1000),
            ]:
                # No assert should be triggered on the following line
                munmap(mmap(f.fileno(), addr, size), size)


if __name__ == "__main__":
    unittest.main()
