import os
import sys
import glob
import cPickle
import logging
import tempfile
try:
    import cStringIO as StringIO
except:
    import StringIO

from contextlib import contextmanager

from .smtlib import solver
from .smtlib.solver import SolverException

logger = logging.getLogger('WORKSPACE')


class StateSerializer(object):
    '''
    StateSerializer can serialize and deserialize :class:`~manticore.core.state.State` objects from and to
    stream-like objects.
    '''
    def __init__(self):
        pass

    def serialize(self, state, f):
        raise NotImplementedError

    def deserialize(self, f):
        raise NotImplementedError

class PickleSerializer(StateSerializer):
    def serialize(self, state, f):
        try:
            f.write(cPickle.dumps(state, 2))
        except RuntimeError:
            # recursion exceeded. try a slower, iterative solution
            from ..utils import iterpickle
            logger.warning("Using iterpickle to dump state")
            f.write(iterpickle.dumps(state, 2))

    def deserialize(self, f):
        return cPickle.load(f)

class Store(object):
    '''
    A Store can save arbitrary keys/values (including states) and file streams. Used for generating
    output, and state saving and loading.

    Implement either save_value/load_value in subclasses, or save_stream/load_stream, or both.
    '''

    def __init__(self, uri, state_serialization_method='pickle'):
        assert self.__class__ != Store, "The Store class can not be instantiated (create a subclass)"

        self.uri = uri
        self._sub = []

        if state_serialization_method == 'pickle':
            self._serializer = PickleSerializer()
        else:
            raise NotImplementedError("Pickling method '{}' not supported.".format(state_serialization_method))


    # save_value/load_value and save_stream/load_stream are implemented in terms of each other. A backing store
    # can choose the pair it's best optimized for.
    def save_value(self, key, value):
        '''
        Save an arbitrary, serializable `value` under `key`.

        :param str key: A string identifier under which to store the value.
        :param value: A serializable value
        :return:
        '''
        with self.save_stream(key) as s:
            s.write(value)

    def load_value(self, key):
        '''
        Load an arbitrary value identified by `key`.

        :param str key: The key that identifies the value
        :return: The loaded value
        '''
        with self.load_stream(key) as s:
            return s.read()

    @contextmanager
    def save_stream(self, key):
        '''
        Return a managed file-like object into which the calling code can write
        arbitrary data.

        :param key:
        :return: A managed stream-like object
        '''
        s = StringIO.StringIO()
        yield s
        self.save_value(key, s.getvalue())

    @contextmanager
    def load_stream(self, key):
        '''
        Return a managed file-like object from which the calling code can read
        previously-serialized data.

        :param key:
        :return: A managed stream-like object
        '''
        value = self.load_value(key)
        yield StringIO.StringIO(value)


    def save_state(self, state, key):
        '''
        Save a state to storage.

        :param state:
        :return:
        '''
        with self.save_stream(key) as f:
            self._serializer.serialize(state, f)

    def load_state(self, key):
        '''

        :param state_id:
        :return:
        '''
        key = 'state_{:08x}.pkl'.format(key)
        with self.load_stream(key) as f:
            state = self._serializer.deserialize(f)
            self.rm(key)
            return state

    def rm(self, key):
        '''
        Remove value identified by `key` from storage.

        :param str key: What to remove
        '''
        raise NotImplementedError

    def ls(self, glob):
        '''
        List all keys in storage

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

    def rm(self, key):
        '''

        :param key:
        :return:
        '''
        path = os.path.join(self.uri, key)
        os.remove(path)

    def ls(self, glob_str):
        '''
        Return just the filenames that match `glob_str` inside the store directory.

        :param glob_str:
        :return:
        '''
        path = os.path.join(self.uri, glob_str)
        return map(lambda s: os.path.split(s)[1], glob.glob(path))


class RedisStore(Store):
    '''
    A redis-backed Manticore workspace
    '''
    def __init__(self, uri=None):
        '''
        :param uri: A url for redis
        '''

        # Local import to not create an explicit dependency
        import redis

        hostname, port = uri.split(':')
        self._client = redis.StrictRedis(host=hostname, port=int(port), db=0)

        super(RedisStore, self).__init__(uri)

    def save_value(self, key, value):
        '''
        Save an arbitrary, serializable `value` under `key`.

        :param str key: A string identifier under which to store the value.
        :param value: A serializable value
        :return:
        '''
        return self._client.set(key, value)

    def load_value(self, key):
        '''
        Load an arbitrary value identified by `key`.

        :param str key: The key that identifies the value
        :return: The loaded value
        '''
        return self._client.get(key)

    def rm(self, key):
        self._client.delete(key)

    def ls(self, glob_str):
        return self._client.keys(glob_str)

def _create_store(desc):
    '''
    Create a :class:`~manticore.core.workspace.Store` instance depending on the descriptor.

    Valid descriptors:
      fs:<path>
      redis:<hostname>:<port>

    :param str desc: Store descriptor
    :return: Store instance
    '''
    type, uri = ('fs', None) if desc is None else desc.split(':', 1)

    if type == 'fs':
        return FilesystemStore(uri)
    elif type == 'redis':
        return RedisStore(uri)
    else:
        raise NotImplementedError("Storage type '%s' not supported.", type)

class Workspace(object):
    '''
    A workspace maintains a list of states to run and assigns them IDs.
    '''

    def __init__(self, lock, desc=None):
        self._store = _create_store(desc)
        self._serializer = PickleSerializer()
        self._last_id = 0
        self._lock = lock
        self._prefix = 'state_'
        self._suffix = '.pkl'

    def try_loading_workspace(self):
        state_names = self._store.ls('{}*'.format(self._prefix))
        def get_state_id(name):
            return int(name[len(self._prefix):-len(self._suffix)], 16)
        state_ids = map(get_state_id, state_names)

        if not state_ids:
            return []

        self._last_id = max(state_ids) + 1

        return state_ids

    def _get_id(self):
        '''
        Get a unique state id.

        :rtype: int
        '''
        try:
            self._lock.acquire()
            id = self._last_id
            self._last_id = id + 1
            return id
        finally:
            self._lock.release()

    def load_state(self, state_id):
        '''
        Load a state from storage identified by `state_id`.

        :param state_id: The state reference of what to load
        :return: The deserialized state
        :rtype: State
        '''
        return self._store.load_state(state_id)

    def save_state(self, state):
        '''
        Save a state to storage, return identifier.

        :param state_id: The state reference of what to load
        :param bool final: Whether the state is finalized (i.e. testcase)
        :return: New state id
        :rtype: int
        '''
        id = self._get_id()
        self._store.save_state(state, '{}{:08x}{}'.format(self._prefix, id, self._suffix))
        return id



class ManticoreOutput(object):
    '''
    Functionality related to producing output. Responsible for generating state summaries,
    coverage information, etc.
    '''
    def __init__(self, desc=None):
        '''
        Create an object capable of producing Manticore output.

        :param desc: A descriptor ('type:uri') of where to write output.
        '''
        self._store = _create_store(desc)
        self._last_id = 0

    @property
    def uri(self):
        return self._store.uri

    def save_testcase(self, state, message=''):
        '''
        Save the environment from `state` to storage. Return a state id
        describing it, which should be an int or a string.

        :param State state: The state to serialize
        :param int testcase_id: Identifier for the state
        :param str state: Optional message to include
        :return: A state id representing the saved state
        '''

        self.save_summary(state, message)
        self.save_trace(state)
        self.save_constraints(state)
        self.save_input_symbols(state)
        self.save_syscall_trace(state)
        self.save_fds(state)
        key = 'test_{:08x}.pkl'.format(self._last_id)
        self._store.save_state(state, key)

        self._last_id += 1

    def save_stream(self, *rest):
        return self._store.save_stream(*rest)

    @contextmanager
    def _named_stream(self, name):
        '''
        Create an indexed output stream i.e. '00000001_name'

        :param name: Identifier for the stream
        :return: A context-managed stream-like object
        '''


        with self._store.save_stream('test_{:08x}.{}'.format(self._last_id, name)) as s:
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

