import os
import sys
import glob
import signal
import logging
import tempfile
import io

from contextlib import contextmanager
from multiprocessing.managers import SyncManager

from ..utils import config
from ..utils.helpers import PickleSerializer
from .smtlib import solver
from .state import StateBase

logger = logging.getLogger(__name__)

consts = config.get_group('workspace')
consts.add('prefix', default='mcore_', description="The prefix to use for output and workspace directories")
consts.add('dir', default='.', description="Location of where to create workspace directories")

_manager = None


def manager():
    global _manager
    if _manager is None:
        _manager = SyncManager()
        _manager.start(lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))
    return _manager


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
        raise NotImplementedError(f"Storage type '{type_}' not supported.")

    def __init__(self, uri, state_serialization_method='pickle'):
        assert self.__class__ != Store, "The Store class can not be instantiated (create a subclass)"

        self.uri = uri
        self._sub = []

        if state_serialization_method == 'pickle':
            self._serializer = PickleSerializer()
        else:
            raise NotImplementedError(f"Pickling method '{state_serialization_method}' not supported.")

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

    def load_value(self, key, binary=False):
        """
        Load an arbitrary value identified by `key`.

        :param str key: The key that identifies the value
        :return: The loaded value
        """
        with self.load_stream(key, binary=binary) as s:
            return s.read()

    @contextmanager
    def save_stream(self, key, binary=False):
        """
        Return a managed file-like object into which the calling code can write
        arbitrary data.

        :param key:
        :return: A managed stream-like object
        """
        s = io.BytesIO() if binary else io.StringIO()
        yield s
        self.save_value(key, s.getvalue())

    @contextmanager
    def load_stream(self, key, binary=False):
        """
        Return a managed file-like object from which the calling code can read
        previously-serialized data.

        :param key:
        :return: A managed stream-like object
        """
        value = self.load_value(key, binary=binary)
        yield io.BytesIO(value) if binary else io.StringIO(value)

    def save_state(self, state, key):
        """
        Save a state to storage.

        :param manticore.core.StateBase state:
        :param str key:
        :return:
        """
        with self.save_stream(key, binary=True) as f:
            self._serializer.serialize(state, f)

    def load_state(self, key, delete=True):
        """
        Load a state from storage.

        :param key: key that identifies state
        :rtype: manticore.core.StateBase
        """
        with self.load_stream(key, binary=True) as f:
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
            uri = os.path.abspath(tempfile.mkdtemp(prefix=consts.prefix, dir=consts.dir))

        if os.path.exists(uri):
            assert os.path.isdir(uri), 'Store must be a directory'
        else:
            os.mkdir(uri)

        super().__init__(uri)

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
    def load_stream(self, key, binary=False):
        """
        :param str key: name of stream to load
        :param bool binary: Whether we should treat it as binary
        :return:
        """
        with open(os.path.join(self.uri, key), 'rb' if binary else 'r') as f:
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
        return [os.path.split(s)[1] for s in glob.glob(path)]


class MemoryStore(Store):
    """
    An in-memory (dict) Manticore workspace.

    NOTE: This is mostly used for experimentation and testing functionality.
    Can not be used with multiple workers!
    """
    store_type = 'mem'

    # TODO(yan): Once we get a global config store, check it to make sure
    # we're executing in a single-worker or test environment.

    def __init__(self, uri=None):
        self._data = {}
        super().__init__(None)

    def save_value(self, key, value):
        self._data[key] = value

    def load_value(self, key, binary=False):
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

        super().__init__(uri)

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
        self._last_id = manager().Value('i', 0)
        self._lock = lock
        self._prefix = 'state_'
        self._suffix = '.pkl'

    def try_loading_workspace(self):
        state_names = self._store.ls(f'{self._prefix}*')

        def get_state_id(name):
            return int(name[len(self._prefix):-len(self._suffix)], 16)

        state_ids = list(map(get_state_id, state_names))

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
        return self._store.load_state(f'{self._prefix}{state_id:08x}{self._suffix}', delete=delete)

    def save_state(self, state, state_id=None):
        """
        Save a state to storage, return identifier.

        :param state: The state to save
        :param int state_id: If not None force the state id potentially overwriting old states
        :return: New state id
        :rtype: int
        """
        assert isinstance(state, StateBase)
        if state_id is None:
            state_id = self._get_id()
        else:
            self.rm_state(state_id)

        self._store.save_state(state, f'{self._prefix}{state_id:08x}{self._suffix}')
        return state_id

    def rm_state(self, state_id):
        """
        Remove a state from storage identified by `state_id`.

        :param state_id: The state reference of what to load
        """
        return self._store.rm(f'{self._prefix}{state_id:08x}{self._suffix}')


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
        self._id_gen = manager().Value('i', self._last_id)
        self._lock = manager().Condition(manager().RLock())

    def testcase(self, prefix='test'):
        class Testcase(object):
            def __init__(self, workspace, prefix):
                self._num = workspace._increment_id()
                self._prefix = prefix
                self._ws = workspace

            @property
            def num(self):
                return self._num

            def open_stream(self, suffix='', binary=False):
                stream_name = f'{self._prefix}_{self._num:08x}.{suffix}'
                return self._ws.save_stream(stream_name, binary=binary)

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
            self._descriptor = f'{self._store.store_type}:{self._store.uri}'

        return self._descriptor

    @sync
    def _increment_id(self):
        self._last_id = self._id_gen.value
        self._id_gen.value += 1
        return self._last_id

    def _named_key(self, suffix):
        return f'{self._named_key_prefix}_{self._last_id:08x}.{suffix}'

    def save_stream(self, key, *rest, **kwargs):
        return self._store.save_stream(key, *rest, **kwargs)

    @contextmanager
    def _named_stream(self, name, binary=False):
        """
        Create an indexed output stream i.e. 'test_00000001.name'

        :param name: Identifier for the stream
        :return: A context-managed stream-like object
        """
        with self._store.save_stream(self._named_key(name), binary=binary) as s:
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
            with self._named_stream(stream_name, binary=True) as stream:
                if isinstance(data, str):
                    data = data.encode()
                stream.write(data)

        self._store.save_state(state, self._named_key('pkl'))
        return self._last_id

    def save_summary(self, state, message):
        with self._named_stream('messages') as summary:
            summary.write(f"Command line:\n  '{' '.join(sys.argv)}'\n")
            summary.write(f'Status:\n  {message}\n\n')

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
                summary.write(f"================ PROC: {idx:02d} ================\n")
                summary.write("Memory:\n")
                if hash(cpu.memory) not in memories:
                    summary.write(str(cpu.memory).replace('\n', '\n  '))
                    memories.add(hash(cpu.memory))

                summary.write(f"CPU:\n{cpu}")

                if hasattr(cpu, "instruction") and cpu.instruction is not None:
                    i = cpu.instruction
                    summary.write(f"  Instruction: 0x{i.address:x}\t{i.mnemonic:s} {i.op_str:s})\n")
                else:
                    summary.write("  Instruction: {symbolic}\n")

    def save_trace(self, state):
        with self._named_stream('trace') as f:
            if 'trace' not in state.context:
                return
            for entry in state.context['trace']:
                f.write(f'0x{entry:x}\n')

    def save_constraints(self, state):
        # XXX(yan): We want to conditionally enable this check
        # assert solver.check(state.constraints)

        with self._named_stream('smt') as f:
            f.write(str(state.constraints))

    def save_input_symbols(self, state):
        with self._named_stream('input') as f:
            for symbol in state.input_symbols:
                buf = solver.get_value(state.constraints, symbol)
                f.write(f'{symbol.name}: {buf!r}\n')
