import os
import sys
import glob
import signal
import cPickle
import logging
import tempfile
try:
    import cStringIO as StringIO
except ImportError:
    import StringIO

from contextlib import contextmanager
from multiprocessing.managers import SyncManager

from .smtlib import solver
from .smtlib.solver import SolverException
from .state import State

logger = logging.getLogger(__name__)

manager = SyncManager()
manager.start(lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))


class StateSerializer(object):
    """
    StateSerializer can serialize and deserialize :class:`~manticore.core.state.State` objects from and to
    stream-like objects.
    """

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
            logger.debug("Using iterpickle to dump state")
            f.write(iterpickle.dumps(state, 2))

    def deserialize(self, f):
        return cPickle.load(f)


class Store(object):
    """
    A `Store` can save arbitrary keys/values (including states) and file streams.
    Used for generating output, state saving and state loading.

    In subclasses:

     * Implement either save_value/load_value, or save_stream/load_stream, or both.
     * Define a `store_type` class variable of type str.
       * This is used as a prefix for a store descriptor
    """

    @classmethod
    def fromdescriptor(cls, desc):
        """
        Create a :class:`~manticore.core.workspace.Store` instance depending on the descriptor.

        Valid descriptors:
          * fs:<path>
          * redis:<hostname>:<port>
          * mem:

        :param str desc: Store descriptor
        :return: Store instance
        """
        type_, uri = ('fs', None) if desc is None else desc.split(':', 1)
        for subclass in cls.__subclasses__():
            if subclass.store_type == type_:
                return subclass(uri)
        raise NotImplementedError("Storage type '{0}' not supported.".format(type_))

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
        """
        Save an arbitrary, serializable `value` under `key`.

        :param str key: A string identifier under which to store the value.
        :param value: A serializable value
        :return:
        """
        with self.save_stream(key) as s:
            s.write(value)

    def load_value(self, key):
        """
        Load an arbitrary value identified by `key`.

        :param str key: The key that identifies the value
        :return: The loaded value
        """
        with self.load_stream(key) as s:
            return s.read()

    @contextmanager
    def save_stream(self, key, *rest, **kwargs):
        """
        Return a managed file-like object into which the calling code can write
        arbitrary data.

        :param key:
        :return: A managed stream-like object
        """
        s = StringIO.StringIO()
        yield s
        self.save_value(key, s.getvalue())

    @contextmanager
    def load_stream(self, key):
        """
        Return a managed file-like object from which the calling code can read
        previously-serialized data.

        :param key:
        :return: A managed stream-like object
        """
        value = self.load_value(key)
        yield StringIO.StringIO(value)

    def save_state(self, state, key):
        """
        Save a state to storage.

        :param manticore.core.State state:
        :param str key:
        :return:
        """
        with self.save_stream(key) as f:
            self._serializer.serialize(state, f)

    def load_state(self, key, delete=True):
        """
        Load a state from storage.

        :param key: key that identifies state
        :rtype: manticore.core.State
        """
        with self.load_stream(key) as f:
            state = self._serializer.deserialize(f)
            if delete:
                self.rm(key)
            return state

    def rm(self, key):
        """
        Remove value identified by `key` from storage.

        :param str key: What to remove
        """
        raise NotImplementedError

    def ls(self, glob_str):
        """
        List all keys in storage

        :return:
        """
        raise NotImplementedError


class FilesystemStore(Store):
    """
    A directory-backed Manticore workspace
    """
    store_type = 'fs'

    def __init__(self, uri=None):
        """
        :param uri: The path to on-disk workspace, or None.
        """
        if not uri:
            uri = os.path.abspath(tempfile.mkdtemp(prefix="mcore_", dir='./'))

        if os.path.exists(uri):
            assert os.path.isdir(uri), 'Store must be a directory'
        else:
            os.mkdir(uri)

        super(FilesystemStore, self).__init__(uri)

    @contextmanager
    def save_stream(self, key, binary=False):
        """
        Yield a file object representing `key`

        :param str key: The file to save to
        :param bool binary: Whether we should treat it as binary
        :return:
        """
        mode = 'wb' if binary else 'w'
        with open(os.path.join(self.uri, key), mode) as f:
            yield f

    @contextmanager
    def load_stream(self, key):
        """
        :param key:
        :return:
        """
        with open(os.path.join(self.uri, key), 'r') as f:
            yield f

    def rm(self, key):
        """
        Remove file identified by `key`.

        :param str key: The file to delete
        """
        path = os.path.join(self.uri, key)
        os.remove(path)

    def ls(self, glob_str):
        """
        Return just the filenames that match `glob_str` inside the store directory.

        :param str glob_str: A glob string, i.e. 'state_*'
        :return: list of matched keys
        """
        path = os.path.join(self.uri, glob_str)
        return map(lambda s: os.path.split(s)[1], glob.glob(path))


class MemoryStore(Store):
    """
    An in-memory (dict) Manticore workspace.

    NOTE: This is mostly used for experimentation and testing funcionality.
    Can not be used with multiple workers!
    """
    store_type = 'mem'

    # TODO(yan): Once we get a global config store, check it to make sure
    # we're executing in a single-worker or test environment.

    def __init__(self, uri=None):
        self._data = {}
        super(MemoryStore, self).__init__(None)

    def save_value(self, key, value):
        self._data[key] = value

    def load_value(self, key):
        return self._data.get(key)

    def rm(self, key):
        del self._data[key]

    def ls(self, glob_str):
        return list(self._data)


class RedisStore(Store):
    """
    A redis-backed Manticore workspace
    """
    store_type = 'redis'

    def __init__(self, uri=None):
        """
        :param uri: A url for redis
        """

        # Local import to avoid an explicit dependency
        import redis

        hostname, port = uri.split(':')
        self._client = redis.StrictRedis(host=hostname, port=int(port), db=0)

        super(RedisStore, self).__init__(uri)

    def save_value(self, key, value):
        """
        Save an arbitrary, serializable `value` under `key`.

        :param str key: A string identifier under which to store the value.
        :param value: A serializable value
        :return:
        """
        return self._client.set(key, value)

    def load_value(self, key):
        """
        Load an arbitrary value identified by `key`.

        :param str key: The key that identifies the value
        :return: The loaded value
        """
        return self._client.get(key)

    def rm(self, key):
        self._client.delete(key)

    def ls(self, glob_str):
        return self._client.keys(glob_str)


# This is copied from Executor to not create a dependency on the naming of the lock field
def sync(f):
    """ Synchronization decorator. """

    def new_function(self, *args, **kw):
        self._lock.acquire()
        try:
            return f(self, *args, **kw)
        finally:
            self._lock.release()
    return new_function


class Workspace(object):
    """
    A workspace maintains a list of states to run and assigns them IDs.
    """

    def __init__(self, lock, store_or_desc=None):
        if isinstance(store_or_desc, Store):
            self._store = store_or_desc
        else:
            self._store = Store.fromdescriptor(store_or_desc)
        self._serializer = PickleSerializer()
        self._last_id = manager.Value('i', 0)
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

        self._last_id.value = max(state_ids) + 1

        return state_ids

    @sync
    def _get_id(self):
        """
        Get a unique state id.

        :rtype: int
        """
        id_ = self._last_id.value
        self._last_id.value += 1
        return id_

    def load_state(self, state_id, delete=True):
        """
        Load a state from storage identified by `state_id`.

        :param state_id: The state reference of what to load
        :return: The deserialized state
        :rtype: State
        """
        return self._store.load_state('{}{:08x}{}'.format(self._prefix, state_id, self._suffix), delete=delete)

    def save_state(self, state, state_id=None):
        """
        Save a state to storage, return identifier.

        :param state: The state to save
        :param int state_id: If not None force the state id potentially overwritting old states
        :return: New state id
        :rtype: int
        """
        assert isinstance(state, State)
        if state_id is None:
            state_id = self._get_id()
        else:
            self.rm_state(state_id)

        self._store.save_state(state, '{}{:08x}{}'.format(self._prefix, state_id, self._suffix))
        return state_id

    def rm_state(self, state_id):
        """
        Remove a state from storage identified by `state_id`.

        :param state_id: The state reference of what to load
        """
        return self._store.rm('{}{:08x}{}'.format(self._prefix, state_id, self._suffix))


class ManticoreOutput(object):
    """
    Functionality related to producing output. Responsible for generating state summaries,
    coverage information, etc.

    Invoked only from :class:`manticore.Manticore` from a single parent process, so
    locking is not required.
    """

    def __init__(self, desc=None):
        """
        Create an object capable of producing Manticore output.

        :param desc: A descriptor ('type:uri') of where to write output.
        """
        self._named_key_prefix = 'test'
        self._descriptor = desc
        self._store = Store.fromdescriptor(desc)
        self._last_id = 0
        self._id_gen = manager.Value('i', self._last_id)
        self._lock = manager.Condition(manager.RLock())

    def testcase(self, prefix='test'):
        class Testcase(object):
            def __init__(self, workspace, prefix):
                self._num = workspace._increment_id()
                self._prefix = prefix
                self._ws = workspace

            @property
            def num(self):
                return self._num

            def open_stream(self, suffix=''):
                stream_name = '{}_{:08x}.{}'.format(self._prefix, self._num, suffix)
                return self._ws.save_stream(stream_name)

        return Testcase(self, prefix)

    @property
    def store(self):
        return self._store

    @property
    def descriptor(self):
        """
        Return a descriptor that created this workspace. Descriptors are of the
        format <type>:<uri>, where type signifies the medium. For example,
          fs:/tmp/workspace
          redis:127.0.0.1:6379

        :rtype: str
        """
        if self._descriptor is None:
            self._descriptor = '{}:{}'.format(self._store.store_type, self._store.uri)

        return self._descriptor

    @sync
    def _increment_id(self):
        self._last_id = self._id_gen.value
        self._id_gen.value += 1
        return self._last_id

    def _named_key(self, suffix):
        return '{}_{:08x}.{}'.format(self._named_key_prefix, self._last_id, suffix)

    def save_stream(self, key, *rest, **kwargs):
        return self._store.save_stream(key, *rest, **kwargs)

    @contextmanager
    def _named_stream(self, name):
        """
        Create an indexed output stream i.e. 'test_00000001.name'

        :param name: Identifier for the stream
        :return: A context-managed stream-like object
        """
        with self._store.save_stream(self._named_key(name)) as s:
            yield s

    #Remove/move ...
    def save_testcase(self, state, prefix, message=''):
        """
        Save the environment from `state` to storage. Return a state id
        describing it, which should be an int or a string.

        :param State state: The state to serialize
        :param str message: The message to add to output
        :return: A state id representing the saved state
        """

        self._named_key_prefix = prefix
        self._increment_id()

        #FIXME this should not be here. Each object must be responsible of
        #formatting its own output
        self.save_summary(state, message)
        self.save_trace(state)
        self.save_constraints(state)
        self.save_input_symbols(state)

        for stream_name, data in state.platform.generate_workspace_files().items():
            with self._named_stream(stream_name) as stream:
                stream.write(data)

        self._store.save_state(state, self._named_key('pkl'))
        return self._last_id

    def save_summary(self, state, message):
        with self._named_stream('messages') as summary:
            summary.write("Command line:\n  '{}'\n" .format(' '.join(sys.argv)))
            summary.write('Status:\n  {}\n\n'.format(message))

            # FIXME(mark) This is a temporary hack for EVM. We need to sufficiently
            # abstract the below code to work on many platforms, not just Linux. Then
            # we can remove this hack.
            if getattr(state.platform, 'procs', None) is None:
                import pprint
                summary.write("EVM World:\n")
                summary.write(pprint.pformat(state.platform._global_storage))
                return

            memories = set()
            for cpu in filter(None, state.platform.procs):
                idx = state.platform.procs.index(cpu)
                summary.write("================ PROC: %02d ================\n" % idx)
                summary.write("Memory:\n")
                if hash(cpu.memory) not in memories:
                    summary.write(str(cpu.memory).replace('\n', '\n  '))
                    memories.add(hash(cpu.memory))

                summary.write("CPU:\n{}".format(cpu))

                if hasattr(cpu, "instruction") and cpu.instruction is not None:
                    i = cpu.instruction
                    summary.write("  Instruction: 0x%x\t(%s %s)\n" % (
                        i.address, i.mnemonic, i.op_str))
                else:
                    summary.write("  Instruction: {symbolic}\n")

    def save_trace(self, state):
        with self._named_stream('trace') as f:
            if 'trace' not in state.context:
                return
            for entry in state.context['trace']:
                f.write('0x{:x}\n'.format(entry))

    def save_constraints(self, state):
        # XXX(yan): We want to conditionally enable this check
        # assert solver.check(state.constraints)

        with self._named_stream('smt') as f:
            f.write(str(state.constraints))

    def save_input_symbols(self, state):
        with self._named_stream('input') as f:
            for symbol in state.input_symbols:
                buf = solver.get_value(state.constraints, symbol)
                f.write('%s: %s\n' % (symbol.name, repr(buf)))

    def save_syscall_trace(self, state):
        with self._named_stream('syscalls') as f:
            f.write(repr(state.platform.syscall_trace))

    def save_fds(self, state):
        def solve_to_fd(data, fd):
            try:
                for c in data:
                    fd.write(chr(solver.get_value(state.constraints, c)))
            except SolverException:
                fd.write('{SolverException}')

        with self._named_stream('stdout') as _out:
            with self._named_stream('stderr') as _err:
                with self._named_stream('stdin') as _in:
                    with self._named_stream('net') as _net:
                        for name, fd, data in state.platform.syscall_trace:
                            if name in ('_transmit', '_write'):
                                if fd == 1:
                                    solve_to_fd(data, _out)
                                elif fd == 2:
                                    solve_to_fd(data, _err)
                            if name in ('_recv'):
                                solve_to_fd(data, _net)
                            if name in ('_receive', '_read') and fd == 0:
                                solve_to_fd(data, _in)
