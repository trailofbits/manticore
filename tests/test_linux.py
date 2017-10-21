import os
import unittest

from manticore.platforms import linux, linux_syscalls


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
        model = self.symbolic_linux
        model.current.memory.mmap(0x1000, 0x1000, 'rw ')
        model.current.SP = 0x2000-4

        # open a file
        filename = model.current.push_bytes('/bin/true\x00')
        fd = model.sys_open(filename, os.O_RDONLY, 0600)

        stat = model.current.SP - 0x100
        model.current.R0 = fd
        model.current.R1 = stat
        model.current.R7 = nr_fstat64
        self.assertEquals(linux_syscalls.armv7[nr_fstat64], 'sys_fstat64')

        model.syscall()

        print ''.join(model.current.read_bytes(stat, 100)).encode('hex')

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
        model = self.symbolic_linux
        model.current.memory.mmap(0x1000, 0x1000, 'rw ')
        model.current.SP = 0x2000-4
        model.current.memory.mmap(0x2000, 0x2000, 'rwx')
        model.current.PC = 0x2000
        model.current.write_int(model.current.PC, 0x050f)

        r = Receiver()
        model.current.subscribe('will_execute_instruction', r.will_exec)
        model.current.subscribe('did_execute_instruction', r.did_exec)

        filename = model.current.push_bytes('/bin/true\x00')
        fd = model.sys_open(filename, os.O_RDONLY, 0600)

        stat = model.current.SP - 0x100
        model.current.R0 = fd
        model.current.R1 = stat
        model.current.R7 = nr_fstat64
        self.assertEquals(linux_syscalls.armv7[nr_fstat64], 'sys_fstat64')

        pre_icount = model.current.icount
        model.execute()
        post_icount = model.current.icount

        self.assertEquals(pre_icount+1, post_icount)
        self.assertEquals(r.nevents, 2)
