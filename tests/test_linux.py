import os
import errno
import shutil
import tempfile
import unittest

from manticore.platforms import linux, linux_syscalls
from manticore.core.smtlib import *
from manticore.core.smtlib import *
from manticore.core.cpu.abstractcpu import ConcretizeRegister


class LinuxTest(unittest.TestCase):
    '''
    TODO(mark): these tests assumes /bin/ls is a dynamic x64 binary
    '''
    _multiprocess_can_split_ = True
    BIN_PATH = '/bin/ls'

    def setUp(self):
        self.linux = linux.Linux(self.BIN_PATH)
        self.symbolic_linux = linux.SLinux.empty_platform('armv7')

    def test_regs_init_state_x86(self):
        x86_defaults = {
            'CS': 0x23,
            'SS': 0x2b,
            'DS': 0x2b,
            'ES': 0x2b,
        }
        cpu = self.linux.current

        for reg, val in x86_defaults.iteritems():
            self.assertEqual(cpu.regfile.read(reg), val)

    def test_stack_init(self):
        argv = ['arg1', 'arg2', 'arg3']
        real_argv = [self.BIN_PATH] + argv
        envp = ['env1', 'env2', 'env3']
        self.linux = linux.Linux(self.BIN_PATH, argv, envp)
        cpu = self.linux.current

        self.assertEqual(cpu.read_int(cpu.STACK), 4)

        argv_ptr = cpu.STACK + 8
        envp_ptr = argv_ptr + len(real_argv)*8 + 8

        for i, arg in enumerate(real_argv):
            self.assertEqual(cpu.read_string(cpu.read_int(argv_ptr + i*8)), arg)

        for i, env in enumerate(envp):
            self.assertEqual(cpu.read_string(cpu.read_int(envp_ptr + i*8)), env)

    def test_load_maps(self):
        mappings = self.linux.current.memory.mappings()

        # stack should be last
        last_map = mappings[-1]
        last_map_perms = last_map[2]
        self.assertEqual(last_map_perms, 'rwx')

        # binary should be first two
        first_map, second_map = mappings[:2]
        first_map_name = first_map[4]
        second_map_name = second_map[4]
        self.assertEqual(first_map_name, '/bin/ls')
        self.assertEqual(second_map_name, '/bin/ls')

    def test_syscall_fstat(self):
        nr_fstat64 = 197

        # Create a minimal state
        platform = self.symbolic_linux
        platform.current.memory.mmap(0x1000, 0x1000, 'rw ')
        platform.current.SP = 0x2000-4

        # open a file
        filename = platform.current.push_bytes('/bin/true\x00')
        fd = platform.sys_open(filename, os.O_RDONLY, 0600)

        stat = platform.current.SP - 0x100
        platform.current.R0 = fd
        platform.current.R1 = stat
        platform.current.R7 = nr_fstat64
        self.assertEquals(linux_syscalls.armv7[nr_fstat64], 'sys_fstat64')

        platform.syscall()

        print ''.join(platform.current.read_bytes(stat, 100)).encode('hex')

    def test_linux_workspace_files(self):
        files = self.symbolic_linux.generate_workspace_files()
        self.assertIn('syscalls', files)
        self.assertIn('stdout', files)
        self.assertIn('stdin', files)
        self.assertIn('stderr', files)
        self.assertIn('net', files)

    def test_syscall_events(self):
        nr_fstat64 = 197

        class Receiver(object):
            def __init__(self):
                self.nevents = 0
            def will_exec(self, pc, i):
                self.nevents += 1
            def did_exec(self, last_pc, pc, i):
                self.nevents += 1

        # Create a minimal state
        platform = self.symbolic_linux
        platform.current.memory.mmap(0x1000, 0x1000, 'rw ')
        platform.current.SP = 0x2000-4
        platform.current.memory.mmap(0x2000, 0x2000, 'rwx')
        platform.current.PC = 0x2000
        platform.current.write_int(platform.current.PC, 0x050f)

        r = Receiver()
        platform.current.subscribe('will_execute_instruction', r.will_exec)
        platform.current.subscribe('did_execute_instruction', r.did_exec)

        filename = platform.current.push_bytes('/bin/true\x00')
        fd = platform.sys_open(filename, os.O_RDONLY, 0600)

        stat = platform.current.SP - 0x100
        platform.current.R0 = fd
        platform.current.R1 = stat
        platform.current.R7 = nr_fstat64
        self.assertEquals(linux_syscalls.armv7[nr_fstat64], 'sys_fstat64')

        pre_icount = platform.current.icount
        platform.execute()
        post_icount = platform.current.icount

        self.assertEquals(pre_icount+1, post_icount)
        self.assertEquals(r.nevents, 2)

    def _create_openat_state(self):
        nr_openat = 322

        # Create a minimal state
        platform = self.symbolic_linux
        platform.current.memory.mmap(0x1000, 0x1000, 'rw ')
        platform.current.SP = 0x2000-4

        dir_path = tempfile.mkdtemp()
        file_name = "file"
        file_path = os.path.join(dir_path, file_name)
        with open(file_path, 'w') as f:
            f.write('test')

        # open a file + directory
        dirname = platform.current.push_bytes(dir_path+'\x00')
        dirfd = platform.sys_open(dirname, os.O_RDONLY, 0700)
        filename = platform.current.push_bytes(file_name+'\x00')

        stat = platform.current.SP - 0x100
        platform.current.R0 = dirfd
        platform.current.R1 = filename
        platform.current.R2 = os.O_RDONLY
        platform.current.R3 = 0700
        platform.current.R7 = nr_openat
        self.assertEquals(linux_syscalls.armv7[nr_openat], 'sys_openat')

        return platform

    def test_syscall_openat_concrete(self):
        platform = self._create_openat_state()

        platform.syscall()

        self.assertGreater(platform.current.R0, 2)

    def test_syscall_openat_symbolic(self):
        platform = self._create_openat_state()

        platform.current.R0 = BitVecVariable(32, 'fd')

        with self.assertRaises(ConcretizeRegister) as cm:
            platform.syscall()

        e = cm.exception

        _min, _max = solver.minmax(platform.constraints, e.cpu.read_register(e.reg_name))
        self.assertLess(_min, len(platform.files))
        self.assertGreater(_max, len(platform.files)-1)


    def test_chroot(self):
        # Create a minimal state
        platform = self.symbolic_linux
        platform.current.memory.mmap(0x1000, 0x1000, 'rw ')
        platform.current.SP = 0x2000-4

        # should error with ENOENT
        this_file = os.path.realpath(__file__)
        path = platform.current.push_bytes('{}\x00'.format(this_file))
        fd = platform.sys_chroot(path)
        self.assertEqual(fd, -errno.ENOTDIR)

        # valid dir, but should always fail with EPERM
        this_dir = os.path.dirname(this_file)
        path = platform.current.push_bytes('{}\x00'.format(this_dir))
        fd = platform.sys_chroot(path)
        self.assertEqual(fd, -errno.EPERM)
