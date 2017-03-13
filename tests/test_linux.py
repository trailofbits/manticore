import unittest

from manticore.models import linux


class LinuxTest(unittest.TestCase):
    BIN_PATH = '/bin/ls'

    def setUp(self):
        self.linux = linux.Linux(self.BIN_PATH)

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
        '''
        TODO(mark): this test assumes /bin/ls is a x64 binary
        '''
        argv = ['arg1', 'arg2', 'arg3']
        real_argv = [self.BIN_PATH] + argv
        envp = ['env1', 'env2', 'env3']
        self.linux = linux.Linux(self.BIN_PATH, argv, envp)
        cpu = self.linux.current

        self.assertEqual(cpu.read_int(cpu.STACK), 4)

        argv_ptr = cpu.STACK + 8
        envp_ptr = argv_ptr + len(real_argv)*8 + 8

        for i, arg in enumerate(real_argv):
            self.assertEqual(self.linux._read_string(cpu, cpu.read_int(argv_ptr + i*8)), arg)

        for i, env in enumerate(envp):
            self.assertEqual(self.linux._read_string(cpu, cpu.read_int(envp_ptr + i*8)), env)
