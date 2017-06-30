import os
import sys
import cPickle
import logging
import tempfile

from contextlib import contextmanager

from .smtlib import solver
from .smtlib.solver import SolverException

logger = logging.getLogger('WORKSPACE')


def _serialize_pickle(state, f):
    '''
    Serialize `state` to file object `f` using cPickle.

    :param state:
    :param f:
    :return:
    '''
    try:
        f.write(cPickle.dumps(state, 2))
    except RuntimeError:
        # recursion exceeded. try a slower, iterative solution
        from ..utils import iterpickle
        logger.warning("Using iterpickle to dump state")
        f.write(iterpickle.dumps(state, 2))


class Store(object):
    '''
    A Store can save arbitrary keys/values and file streams. Used for producing
    output, and state saving and loading.
    '''

    def __init__(self, uri, state_serialization_method='pickle'):
        self.uri = uri

        if state_serialization_method == 'pickle':
            self._serialize = lambda self, *args: _serialize_pickle(*args)
        else:
            raise NotImplementedError("Pickling method '{}' not supported.".format(state_serialization_method))

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

    @contextmanager
    def save_stream(self, key):
        '''
        Return a managed file-like object into which the calling code can write
        arbitrary data.

        :param key:
        :return: A managed stream-like object
        '''
        raise NotImplementedError

    @contextmanager
    def load_stream(self, key):
        '''
        Return a managed file-like object from which the calling code can read
        previously-serialized data.

        :param key:
        :return: A managed stream-like object
        '''
        raise NotImplementedError

    def save_state(self, state, key):
        '''
        Save a state to storage.

        :param state:
        :return:
        '''
        with self.save_stream(key) as f:
            self._method(state, f)


    def load_state(self, key):
        '''

        :param state_id:
        :return:
        '''
        pass

    def list_keys(self, prefix):
        '''

        :param prefix:
        :return:
        '''
        raise NotImplementedError

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

        super(FilesystemStore, self).__init__(uri)

    @contextmanager
    def save_stream(self, key, binary=False):
        '''

        :param key:
        :return:
        '''
        mode = 'w{}'.format('b' if binary else '')
        with open(os.path.join(self.uri, key), mode) as f:
            yield f

    @contextmanager
    def load_stream(self, key):
        '''
        :param key:
        :return:
        '''
        with open(os.path.join(self.uri, key), 'r') as f:
            yield f

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

class RedisStore(Store):
    def __init__(selfself, uri=None):
        pass

def _create_store(desc):
    type, uri = ('fs', None) if desc is None else desc.split(':', 1)

    if type == 'fs':
        return FilesystemStore(uri)
    elif type == 'redis':
        return RedisStore(uri)
    else:
        raise NotImplementedError("Storage type '%s' not supported.", type)

class Workspace(object):

    def __init__(self, desc=None):
        self._store = _create_store(desc)
        self._last_id = 0

    def _try_loading_workspace(self):
        pass

    def load_state(self, state_id):
        '''
        Load a state from storage identified by `state_id`.

        :param state_id: The state reference of what to load
        :return: The deserialized state
        :rtype: State
        '''
        raise NotImplementedError

    def save_state(self, state, final=True):
        '''
        Save a state to storage, return identifier.

        :param state_id: The state reference of what to load
        :param bool final: Whether the state is finalized (i.e. testcase)
        :return: The deserialized state
        :rtype: State
        '''
        raise NotImplementedError

class ManticoreOutput(object):
    '''
    Base class for Manticore output. Responsible for generating execution-based
    output, such as state summaries, coverage information, etc.
    '''

    def __init__(self, desc=None):
        '''
        Create an object capable of producing Manticore output.

        :param desc: A descriptor ('type:uri') of where to write output.
        '''
        self._store = _create_store(desc)

    @property
    def uri(self):
        return self._store.uri

    def save_testcase(self, state, testcase_id, message=''):
        '''
        Save the environment from `state` to storage. Return a state id
        describing it, which should be an int or a string.

        :param State state: The state to serialize
        :param int testcase_id: Identifier for the state
        :param str state: Optional message to include
        :return: A state id representing the saved state
        '''

        self._last_id = testcase_id

        self.save_summary(state, message)
        self.save_trace(state)
        self.save_constraints(state)
        self.save_input_symbols(state)
        self.save_syscall_trace(state)
        self.save_fds(state)

    @contextmanager
    def _named_stream(self, name):
        '''
        Create an indexed output stream i.e. '00000001_name'

        :param name: Identifier for the stream
        :return: A context-managed stream-like object
        '''
        with self._store.save_stream('{:08x}.{}'.format(self._last_id, name)) as s:
            yield s

    def save_summary(self, state, message):
        with self._named_stream('messages') as summary:
            summary.write("Command line:\n  '{}'\n" .format(' '.join(sys.argv)))
            summary.write('Status:\n  {}\n\n'.format(message))

            memories = set()
            for cpu in filter(None, state.platform.procs):
                idx = state.platform.procs.index(cpu)
                summary.write("================ PROC: %02d ================\n"%idx)
                summary.write("Memory:\n")
                if hash(cpu.memory) not in memories:
                    summary.write(str(cpu.memory).replace('\n', '\n  '))
                    memories.add(hash(cpu.memory))

                summary.write("CPU:\n{}".format(cpu))

                if hasattr(cpu, "instruction") and cpu.instruction is not None:
                    i = cpu.instruction
                    summary.write("  Instruction: 0x%x\t(%s %s)\n"%(
                        i.address, i.mnemonic, i.op_str))
                else:
                    summary.write("  Instruction: {symbolic}\n")

    def save_trace(self, state):
        with self._named_stream('trace') as f:
            for pc in state.context['visited']:
                f.write('0x{:08x}\n'.format(pc))

    def save_constraints(self, state):
        # XXX(yan): We want to conditionally enable this check
        assert solver.check(state.constraints)

        with self._named_stream('smt') as f:
            f.write(str(state.constraints))

    def save_input_symbols(self, state):
        with self._named_stream('txt') as f:
            for symbol in state.input_symbols:
                buf = solver.get_value(state.constraints, symbol)
                f.write('%s: %s\n'%(symbol.name, repr(buf)))

    def save_syscall_trace(self, state):
        with self._named_stream('syscalls') as f:
            f.write(repr(state.platform.syscall_trace))

    def save_fds(self, state):
        with self._named_stream('stdout') as _out:
         with self._named_stream('stdout') as _err:
          with self._named_stream('stdin') as _in:
              for name, fd, data in state.platform.syscall_trace:
                  if name in ('_transmit', '_write'):
                      if   fd == 1: _out.write(''.join(str(c) for c in data))
                      elif fd == 2: _err.write(''.join(str(c) for c in data))
                  if name in ('_receive', '_read') and fd == 0:
                      try:
                          for c in data:
                              _in.write(chr(solver.get_value(state.constraints, c)))
                      except SolverException, e:
                          _in.write('{SolverException}')

