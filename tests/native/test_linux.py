import errno
import unittest
from binascii import hexlify

import os
import shutil
import tempfile
import re


from manticore.native.cpu.abstractcpu import ConcretizeRegister
from manticore.core.smtlib.solver import Z3Solver
from manticore.core.smtlib import BitVecVariable, issymbolic
from manticore.native import Manticore
from manticore.platforms import linux, linux_syscalls
from manticore.utils.helpers import pickle_dumps
from manticore.platforms.linux import EnvironmentError


class LinuxTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    BIN_PATH = os.path.join(os.path.dirname(__file__), "binaries", "basic_linux_amd64")

    def setUp(self) -> None:
        self.linux = linux.Linux(self.BIN_PATH)
        self.symbolic_linux_armv7 = linux.SLinux.empty_platform("armv7")
        self.symbolic_linux_aarch64 = linux.SLinux.empty_platform("aarch64")

    def tearDown(self) -> None:
        for p in [self.linux, self.symbolic_linux_armv7, self.symbolic_linux_aarch64]:
            for entry in p.fd_table.entries():
                entry.fdlike.close()

    def test_regs_init_state_x86(self) -> None:
        x86_defaults = {"CS": 0x23, "SS": 0x2B, "DS": 0x2B, "ES": 0x2B}
        cpu = self.linux.current

        for reg, val in x86_defaults.items():
            self.assertEqual(cpu.regfile.read(reg), val)

    def test_stack_init(self) -> None:
        argv = ["arg1", "arg2", "arg3"]
        real_argv = [self.BIN_PATH] + argv
        envp = ["env1", "env2", "env3"]
        self.linux = linux.Linux(self.BIN_PATH, argv, envp)
        cpu = self.linux.current

        self.assertEqual(cpu.read_int(cpu.STACK), 4)

        argv_ptr = cpu.STACK + 8
        envp_ptr = argv_ptr + len(real_argv) * 8 + 8

        for i, arg in enumerate(real_argv):
            self.assertEqual(cpu.read_string(cpu.read_int(argv_ptr + i * 8)), arg)

        for i, env in enumerate(envp):
            self.assertEqual(cpu.read_string(cpu.read_int(envp_ptr + i * 8)), env)

    def test_load_maps(self) -> None:
        mappings = self.linux.current.memory.mappings()

        # stack should be last
        last_map = mappings[-1]
        last_map_perms = last_map[2]
        self.assertEqual(last_map_perms, "rwx")

        # binary should be first two
        first_map, second_map = mappings[:2]
        first_map_name = os.path.basename(first_map[4])
        second_map_name = os.path.basename(second_map[4])
        self.assertEqual(first_map_name, "basic_linux_amd64")
        self.assertEqual(second_map_name, "basic_linux_amd64")

    def test_load_proc_self_maps(self) -> None:
        proc_maps = self.linux.current.memory.proc_self_mappings()

        # check that proc self raises error when not being read created as read only
        maps = self.linux.current.push_bytes("/proc/self/maps\x00")
        self.assertRaises(EnvironmentError, self.linux.sys_open, maps, os.O_RDWR, None)
        self.assertRaises(EnvironmentError, self.linux.sys_open, maps, os.O_WRONLY, None)

        # addresses should be in ascending order
        for i in range(1, len(proc_maps)):
            self.assertLess(proc_maps[i - 1].start, proc_maps[i].start)
            self.assertLess(proc_maps[i - 1].end, proc_maps[i].end)

        for m in proc_maps:
            # check all properties are initialized
            self.assertNotEqual(m.start, None)
            self.assertNotEqual(m.end, None)
            self.assertNotEqual(m.perms, None)
            self.assertNotEqual(m.offset, None)
            self.assertNotEqual(m.device, None)
            self.assertNotEqual(m.inode, None)
            self.assertNotEqual(m.pathname, None)

            # check that address and perms properties are working and properly formatted
            self.assertNotEqual(re.fullmatch(r"[0-9a-f]{16}\-[0-9a-f]{16}", m.address), None)
            self.assertNotEqual(re.fullmatch(r"[r-][w-][x-][sp-]", m.perms), None)
            self.assertNotEqual(
                re.fullmatch(
                    r"[0-9a-f]{16}-[0-9a-f]{16} [r-][w-][x-][sp-] [0-9a-f]{8} [0-9a-f]{2}:[0-9a-f]{2} (?=.{9})\ *\d+ [^\n]*",
                    str(m),
                ),
                None,
            )

    def test_aarch64_syscall_write(self) -> None:
        nr_write = 64

        # Create a minimal state.
        platform = self.symbolic_linux_aarch64
        platform.current.memory.mmap(0x1000, 0x1000, "rw ")
        platform.current.SP = 0x2000 - 8

        # Create a buffer.
        buf = platform.current.SP - 0x100
        s = "hello\n"
        platform.current.write_bytes(buf, s)

        fd = 1  # stdout
        size = len(s)

        # Invoke the syscall.
        platform.current.X0 = fd
        platform.current.X1 = buf
        platform.current.X2 = size
        platform.current.X8 = nr_write
        self.assertEqual(linux_syscalls.aarch64[nr_write], "sys_write")

        platform.syscall()

        self.assertEqual(platform.current.regfile.read("X0"), size)

        res = "".join(map(chr, platform.output.read(size)))
        self.assertEqual(res, s)

    @unittest.skip("Stat differs in different test environments")
    def test_armv7_syscall_fstat(self) -> None:
        nr_fstat64 = 197

        # Create a minimal state
        platform = self.symbolic_linux_armv7
        platform.current.memory.mmap(0x1000, 0x1000, "rw ")
        platform.current.SP = 0x2000 - 4

        # open a file
        filename = platform.current.push_bytes("/\x00")
        fd = platform.sys_open(filename, os.O_RDONLY, 0o600)

        stat = platform.current.SP - 0x100
        platform.current.R0 = fd
        platform.current.R1 = stat
        platform.current.R7 = nr_fstat64
        self.assertEqual(linux_syscalls.armv7[nr_fstat64], "sys_fstat64")

        platform.syscall()
        self.assertEqual(
            b"02030100000000000200000000000000ed41000018000000000000000000000000000000000000000000000000000000001000000000000000100000000000000800000000000000e5c1bc5c15e85e260789ab5c8cd5db350789ab5c8cd5db3500000000",
            hexlify(b"".join(platform.current.read_bytes(stat, 100))),
        )

    def test_armv7_linux_symbolic_files_workspace_files(self) -> None:
        fname = "symfile"
        platform = self.symbolic_linux_armv7

        # create symbolic file
        with open(fname, "w") as f:
            f.write("+")

        # tell manticore it's symbolic
        platform.add_symbolic_file(fname)

        # create filename in memory
        platform.current.memory.mmap(0x1000, 0x1000, "rw ")
        platform.current.SP = 0x2000 - 4
        fname_ptr = platform.current.push_bytes(fname + "\x00")

        # open and close file
        fd = platform.sys_open(fname_ptr, os.O_RDWR, 0o600)
        platform.sys_close(fd)

        # trigger testcase generation
        files = platform.generate_workspace_files()

        # clean up that file we made
        os.remove(fname)

        # make sure we generate a workspace file for that symbolic file
        self.assertIn(fname, files)
        self.assertEqual(len(files[fname]), 1)

    def test_armv7_linux_workspace_files(self) -> None:
        platform = self.symbolic_linux_armv7
        platform.argv = ["arg1", "arg2"]

        files = platform.generate_workspace_files()
        self.assertIn("syscalls", files)
        self.assertIn("argv", files)
        self.assertEqual(files["argv"], b"arg1\narg2\n")
        self.assertIn("env", files)
        self.assertIn("stdout", files)
        self.assertIn("stdin", files)
        self.assertIn("stderr", files)
        self.assertIn("net", files)

    def test_armv7_syscall_events(self) -> None:
        nr_fstat64 = 197

        class Receiver:
            def __init__(self):
                self.nevents = 0

            def will_exec(self, pc, i):
                self.nevents += 1

            def did_exec(self, last_pc, pc, i):
                self.nevents += 1

        # Create a minimal state
        platform = self.symbolic_linux_armv7
        platform.current.memory.mmap(0x1000, 0x1000, "rw ")
        platform.current.SP = 0x2000 - 4
        platform.current.memory.mmap(0x2000, 0x2000, "rwx")
        platform.current.PC = 0x2000
        platform.current.write_int(platform.current.PC, 0x050F)

        r = Receiver()
        platform.current.subscribe("will_execute_instruction", r.will_exec)
        platform.current.subscribe("did_execute_instruction", r.did_exec)

        filename = platform.current.push_bytes("/bin/true\x00")
        fd = platform.sys_open(filename, os.O_RDONLY, 0o600)

        stat = platform.current.SP - 0x100
        platform.current.R0 = fd
        platform.current.R1 = stat
        platform.current.R7 = nr_fstat64
        self.assertEqual(linux_syscalls.armv7[nr_fstat64], "sys_fstat64")

        pre_icount = platform.current.icount
        platform.execute()
        post_icount = platform.current.icount

        self.assertEqual(pre_icount + 1, post_icount)
        self.assertEqual(r.nevents, 2)

    def _armv7_create_openat_state(self):
        nr_openat = 322

        # Create a minimal state
        platform = self.symbolic_linux_armv7
        platform.current.memory.mmap(0x1000, 0x1000, "rw ")
        platform.current.SP = 0x2000 - 4

        dir_path = tempfile.mkdtemp()
        file_name = "file"
        file_path = os.path.join(dir_path, file_name)
        with open(file_path, "wb") as f:
            f.write(b"test")

        # open a file + directory
        dirname = platform.current.push_bytes(dir_path + "\x00")
        dirfd = platform.sys_open(dirname, os.O_RDONLY, 0o700)
        filename = platform.current.push_bytes(file_name + "\x00")

        stat = platform.current.SP - 0x100
        platform.current.R0 = dirfd
        platform.current.R1 = filename
        platform.current.R2 = os.O_RDONLY
        platform.current.R3 = 0o700
        platform.current.R7 = nr_openat
        self.assertEqual(linux_syscalls.armv7[nr_openat], "sys_openat")

        return platform, dir_path

    def test_armv7_syscall_openat_concrete(self) -> None:
        platform, temp_dir = self._armv7_create_openat_state()
        try:
            platform.syscall()
            self.assertGreater(platform.current.R0, 2)
        finally:
            shutil.rmtree(temp_dir)

    def test_armv7_syscall_openat_symbolic(self) -> None:
        platform, temp_dir = self._armv7_create_openat_state()
        try:
            platform.current.R0 = platform.constraints.new_bitvec(32, "fd")

            with self.assertRaises(ConcretizeRegister) as cm:
                platform.syscall()

            e = cm.exception

            _min, _max = Z3Solver.instance().minmax(
                platform.constraints, e.cpu.read_register(e.reg_name)
            )
            self.assertLess(_min, len(platform.fd_table.entries()))
            self.assertGreater(_max, len(platform.fd_table.entries()) - 1)
        finally:
            shutil.rmtree(temp_dir)

    def test_armv7_chroot(self) -> None:
        # Create a minimal state
        platform = self.symbolic_linux_armv7
        platform.current.memory.mmap(0x1000, 0x1000, "rw ")
        platform.current.SP = 0x2000 - 4

        # should error with ENOENT
        this_file = os.path.realpath(__file__)
        path = platform.current.push_bytes(f"{this_file}\x00")
        fd = platform.sys_chroot(path)
        self.assertEqual(fd, -errno.ENOTDIR)

        # valid dir, but should always fail with EPERM
        this_dir = os.path.dirname(this_file)
        path = platform.current.push_bytes(f"{this_dir}\x00")
        fd = platform.sys_chroot(path)
        self.assertEqual(fd, -errno.EPERM)

    def test_symbolic_argv_envp(self) -> None:
        dirname = os.path.dirname(__file__)
        self.m = Manticore.linux(
            os.path.join(dirname, "binaries", "arguments_linux_amd64"),
            argv=["+"],
            envp={"TEST": "+"},
        )

        for state in self.m.all_states:
            ptr = state.cpu.read_int(state.cpu.RSP + (8 * 2))  # get argv[1]
            mem = state.cpu.read_bytes(ptr, 2)
            self.assertTrue(issymbolic(mem[0]))
            self.assertEqual(mem[1], b"\0")

            ptr = state.cpu.read_int(state.cpu.RSP + (8 * 4))  # get envp[0]
            mem = state.cpu.read_bytes(ptr, 7)
            self.assertEqual(b"".join(mem[:5]), b"TEST=")
            self.assertEqual(mem[6], b"\0")
            self.assertTrue(issymbolic(mem[5]))

    def test_serialize_state_with_closed_files(self) -> None:
        # regression test: issue 954

        platform = self.linux
        filename = platform.current.push_bytes("/bin/true\x00")
        fd = platform.sys_open(filename, os.O_RDONLY, 0o600)
        platform.sys_close(fd)
        pickle_dumps(platform)

    def test_thumb_mode_entrypoint(self) -> None:
        # thumb_mode_entrypoint is a binary with only one instruction
        #   0x1000: add.w   r0, r1, r2
        # which is a Thumb instruction, so the entrypoint is set to 0x1001
        m = Manticore.linux(
            os.path.join(os.path.dirname(__file__), "binaries", "thumb_mode_entrypoint")
        )
        m.context["success"] = False

        @m.init
        def init(state):
            state.platform.current.regfile.write("R0", 0)
            state.platform.current.regfile.write("R1", 0x1234)
            state.platform.current.regfile.write("R2", 0x5678)

        @m.hook(0x1001)
        def pre(state):
            # If the wrong PC value was used by the loader (0x1001 instead of 0x1000),
            # the wrong instruction bytes will have been fetched from memory
            state.abandon()

        @m.hook(0x1004)
        def post(state):
            # If the wrong execution mode was set by the loader, the wrong instruction
            # will have been executed, so the register value will be incorrect
            with m.locked_context() as ctx:
                ctx["success"] = state.cpu.regfile.read("R0") == 0x68AC
            state.abandon()

        m.run()
        self.assertTrue(m.context["success"])
