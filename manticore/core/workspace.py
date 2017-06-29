import os
import sys
import logging
import tempfile

from contextlib import contextmanager

from .smtlib import solver
from .smtlib.solver import SolverException

logger = logging.getLogger('WORKSPACE')

class Store(object):

    @classmethod
    def create_store(cls, type, uri):
        return _create_store(type, uri)

    def __init__(self, uri):
        self._uri = uri

    def save_value(self, key, value):
        '''
        Save an arbitrary, serializable `value` under `key`.

        :param str key: A string identifier under which to store the value.
        :param value: A serializable value
        :return:
        '''
        raise NotImplementedError

    def load_value(self, key):
        '''
        Load an arbitrary value identified by `key`.

        :param str key: The key that identifies the value
        :return: The loaded value
        '''
        raise NotImplementedError

    def saved_stream(self, key):
        '''
        Return a managed file-like object into which the calling code can write
        arbitrary data.

        :param key:
        :return: A managed stream-like object
        '''
        raise NotImplementedError

    def loaded_stream(self, key):
        '''
        Return a managed file-like object from which the calling code can read
        previously-serialized data.

        :param key:
        :return: A managed stream-like object
        '''
        raise NotImplementedError


class Output(object):
    pass

class Workspace(object):
    pass

class Workspace(Store):
    '''
    Base class for Manticore workspaces. Responsible for saving and loading
    states, and arbitrary values.
    '''

    def __init__(self, uri):
        self._uri = uri


    def save_testcase(self, state, testcase_id):
        '''
        Save the environment from `state` to storage. Return a state id
        describing it, which should be an int or a string.

        :param State state: The state to serialize
        :return: A state id representing the saved state
        '''
        self.save_summary(state)
        self.save_trace(state)
        self.save_constraints(state)
        self.save_input_symbols(state)
        self.save_syscall_trace(state)
        self.save_fds(state)

    def load_state(self, state_id):
        '''
        Load a state from storage identified by `state_id`.

        :param state_id: The state reference of what to load
        :return: The deserialized state
        :rtype: State
        '''
        raise NotImplementedError

    def save_summary(self, state, message):
        memories = set()

        with self.saved_stream('test_%08x.messages'%self.id) as summary:
            summary.write("Command line:\n  " + ' '.join(sys.argv) + '\n')
            summary.write('Status:\n  {}\n'.format(message))
            summary.write('\n')

            for cpu in filter(None, state.platform.procs):
                idx = state.platform.procs.index(cpu)
                summary.write("================ PROC: %02d ================\n"%idx)
                summary.write("Memory:\n")
                if hash(cpu.memory) not in memories:
                    for m in str(cpu.memory).split('\n'):
                        summary.write("  %s\n"%m)
                    memories.add(hash(cpu.memory))

                summary.write("CPU:\n{}".format(cpu))

                if hasattr(cpu, "instruction") and cpu.instruction is not None:
                    i = cpu.instruction
                    summary.write("  Instruction: 0x%x\t(%s %s)\n"%(
                        i.address, i.mnemonic, i.op_str))
                else:
                    summary.write("  Instruction: {symbolic}\n")

    def save_trace(self, state):
        with self.saved_stream('test_%08x.trace'%self.id) as f:
            for pc in state.context['visited']:
                f.write('0x{:08x}\n'.format(pc))

    def save_constraints(self, state):
        # XXX(yan): We want to conditionally enable this check
        assert solver.check(state.constraints)

        with self.saved_stream('test_%08x.smt'%self.id) as f:
            f.write(str(state.constraints))

    def save_input_symbols(self, state):
        with self.saved_stream('test_%08x.txt'%self.id) as f:
            for symbol in state.input_symbols:
                buf = solver.get_value(state.constraints, symbol)
                f.write('%s: %s\n'%(symbol.name, repr(buf)))

    def save_syscall_trace(self, state):
        with self.saved_stream('test_%08x.syscalls'%self.id) as f:
            f.write(state.platform.syscall_trace)

    def save_fds(self, state):
        with self.saved_stream('test_%08x.stdout'%self.id) as _out:
         with self.saved_stream('test_%08x.stdout'%self.id) as _err:
          with self.saved_stream('test_%08x.stdin'%self.id) as _in:
              for name, fd, data in state.platform.syscall_trace:
                  if name in ('_transmit', '_write'):
                      if   fd == 1: _out.write(map(str, data))
                      elif fd == 2: _err.write(map(str, data))
                   if name in ('_receive', '_read') and fd == 0:
                       try:
                           for c in data:
                               _in.write(chr(solver.get_value(state.constraints, c)))
                       except SolverException, e:
                           _in.write('{SolverException}')



class FilesystemStore(Store):
    '''
    A directory-backed Manticore workspace
    '''
    def __init__(self, uri=None):
        '''

        :param uri: The path to on-disk workspace, or None.
        '''
        if uri is None:
            uri = os.path.abspath(tempfile.mkdtemp(prefix="mcore_", dir='./'))

        if os.path.exists(uri):
            assert os.path.isdir(uri), 'Workspace must be a directory'
        else:
            os.mkdir(uri)

        self._uri = os.path.abspath(uri)

        logger.debug("Workspace set: %s", self._uri)

    def save_state(self, state):
        super(FilesystemWorkspace, self).save_state(state)

    def load_state(self, state_id):
        super(FilesystemWorkspace, self).load_state(state_id)

    @contextmanager
    def saved_stream(self, key):
        '''

        :param key:
        :return:
        '''
        with open(os.path.join(self._uri, key)) as f:
            yield f


def _create_store(type, uri):
    if type == 'fs':
        FilesystemStore(uri)
    else:
        raise NotImplementedError("Workspace type '%s' not supported.", type)
