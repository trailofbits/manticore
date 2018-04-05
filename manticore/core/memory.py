from abc import ABCMeta, abstractmethod, abstractproperty
from weakref import WeakValueDictionary
from .smtlib import *
import logging
from ..utils.mappings import _mmap, _munmap
from ..utils.helpers import issymbolic

logger = logging.getLogger(__name__)


class MemoryException(Exception):
    '''
    Memory exceptions
    '''

    def __init__(self, message, address=None):
        '''
        Builds a memory exception.

        :param message: exception message.
        :param address: memory address where the exception occurred.
        '''
        self.address = address
        self.message = message
        if address is not None and not issymbolic(address):
            self.message += ' <{:x}>'.format(address)

    def __str__(self):
        return self.message


class ConcretizeMemory(MemoryException):
    '''
    Raised when a symbolic memory cell needs to be concretized.
    '''

    def __init__(self, mem, address, size, policy='MINMAX'):
        self.message = "Concretizing memory address {} size {}".format(address, size)
        self.mem = mem
        self.address = address
        self.size = size
        self.policy = policy


class InvalidMemoryAccess(MemoryException):
    _message = 'Invalid memory access'

    def __init__(self, address, mode):
        assert mode in 'rwx'
        suffix = ' (mode:{})'.format(mode)
        message = self._message + suffix
        super(InvalidMemoryAccess, self, ).__init__(message, address)
        self.mode = mode


class InvalidSymbolicMemoryAccess(InvalidMemoryAccess):
    _message = 'Invalid symbolic memory access'

    def __init__(self, address, mode, size, constraint):
        super(InvalidSymbolicMemoryAccess, self, ).__init__(address, mode)
        # the crashing constraint you need to assert
        self.constraint = constraint
        self.size = size


class Map(object):
    '''
    A memory map.

    It represents a convex chunk of memory with a start and an end address.
    It may be implemented as an actual file mapping or as a StringIO/bytearray.

    >>>           ######################################
                  ^                                    ^
                start                                 end

    '''
    __metaclass__ = ABCMeta

    def __init__(self, start, size, perms, name=None):
        '''
        Abstract memory map.

        :param start: the first valid address.
        :param size: the size of the map.
        :param perms: the access permissions of the map (rwx).
        '''
        assert isinstance(start, (int, long)) and start >= 0, 'Invalid start address'
        assert isinstance(size, (int, long)) and size > 0, 'Invalid end address'

        super(Map, self).__init__()
        self._start = start
        self._end = start + size
        self._set_perms(perms)
        self._name = name

    def _get_perms(self):
        ''' Gets the access permissions of the map. '''
        return self._perms

    def _set_perms(self, perms):
        '''
        Sets the access permissions of the map.

        :param perms: the new permissions.
        '''
        assert isinstance(perms, str) and len(perms) <= 3 and perms.strip() in ['', 'r', 'w', 'x', 'rw', 'r x', 'rx', 'rwx', 'wx', ]
        self._perms = perms

    # Property
    perms = property(_get_perms, _set_perms)

    def access_ok(self, access):
        ''' Check if there is enough permissions for access '''
        for c in access:
            if c not in self.perms:
                return False
        return True

    @property
    def start(self):
        return self._start

    @property
    def end(self):
        return self._end

    @property
    def name(self):
        return self._name

    def __len__(self):
        '''Returns the current size in bytes. '''
        return self._end - self._start

    def __repr__(self):
        '''
        Returns the string representation of the map mapping.

        :rtype: str
        '''
        return '<%s 0x%016x-0x%016x %s>' % (self.__class__.__name__, self.start, self.end, self.perms)

    def __cmp__(self, other):
        result = cmp(self.start, other.start)
        if result != 0:
            return result
        result = cmp(self.end, other.end)
        if result != 0:
            return result
        # go by each char permission
        result = cmp(self.perms, other.perms)
        if result != 0:
            return result
        return cmp(self.name, other.name)

    def _in_range(self, index):
        ''' Returns True if index is in range '''
        if isinstance(index, slice):
            in_range = index.start < index.stop and \
                index.start >= self.start and \
                index.stop <= self.end
        else:
            in_range = index >= self.start and \
                index <= self.end
        return in_range

    def _get_offset(self, index):
        '''
        Translates the index to the internal offsets.

        self.start   -> 0
        self.start+1 -> 1
        ...
        self.end     -> len(self)
        '''
        if not self._in_range(index):
            raise IndexError('Map index out of range')
        if isinstance(index, slice):
            index = slice(index.start - self.start, index.stop - self.start)
        else:
            index -= self.start
        return index

    @abstractmethod
    def __getitem__(self, index):
        '''
        Reads a byte from an address or a sequence of bytes from a range of addresses

        :param index: the address or slice where to obtain the bytes from.
        :return: the character or sequence at the specified address.
        :rtype: byte or array
        '''

    @abstractmethod
    def __setitem__(self, index, value):
        '''
        Writes a byte to an address or a sequence of bytes to a range of addresses

        :param index: the address or slice where to put the data.
        :param value: byte or sequence of bytes to put in this map.
        '''

    @abstractmethod
    def split(self, address):
        '''
        Split the current map into two mappings

        :param address: The address at which to split the Map.
        '''


class AnonMap(Map):
    ''' A concrete anonymous memory map '''

    def __init__(self, start, size, perms, data_init=None, **kwargs):
        '''
        Builds a concrete anonymous memory map.

        :param start: the first valid address of the map.
        :param size: the size of the map.
        :param perms: the access permissions of the map.
        :param data_init: the data to initialize the map.
        '''
        super(AnonMap, self).__init__(start, size, perms, **kwargs)
        self._data = bytearray(size)
        if data_init is not None:
            assert len(data_init) <= size, 'More initial data than reserved memory'
            self._data[0:len(data_init)] = data_init

    def __reduce__(self):
        return (self.__class__, (self.start, len(self), self.perms, self._data, ))

    def split(self, address):
        if address <= self.start:
            return None, self
        if address >= self.end:
            return self, None

        assert address > self.start and address < self.end
        head = AnonMap(self.start, address - self.start, self.perms, self[self.start:address])
        tail = AnonMap(address, self.end - address, self.perms, self[address:self.end])
        return head, tail

    def __setitem__(self, index, value):
        assert not isinstance(index, slice) or \
            len(value) == index.stop - index.start
        index = self._get_offset(index)
        self._data[index] = value

    def __getitem__(self, index):
        index = self._get_offset(index)
        if isinstance(index, slice):
            return map(chr, self._data[index])
        return chr(self._data[index])


class FileMap(Map):
    '''
    A file map.

    A  file is mapped in multiples of the page size.  For a file that is not a
    multiple of the page size, the remaining memory is zeroed when mapped, and
    writes to that region are not written out to the file. The effect of
    changing the size of the underlying file of a mapping on the pages that
    correspond to added or removed regions of the file is unspecified.
    '''

    def __init__(self, addr, size, perms, filename, offset=0, overlay=None, **kwargs):
        '''
        Builds a map of memory  initialized with the content of filename.

        :param addr: the first valid address of the file map.
        :param size: the size of the file map.
        :param perms: the access permissions of the file map.
        :param filename: the file to map in memory.
        :param offset: the offset into the file where to start the mapping. \
                This offset must be a multiple of pagebitsize.
        '''
        super(FileMap, self).__init__(addr, size, perms, **kwargs)
        assert isinstance(offset, (int, long))
        assert offset >= 0
        self._filename = filename
        self._offset = offset
        with open(filename, 'r') as fileobject:
            fileobject.seek(0, 2)
            file_size = fileobject.tell()
            self._mapped_size = min(size, file_size - offset)
            self._data = _mmap(fileobject.fileno(), offset, self._mapped_size)
        if overlay is not None:
            self._overlay = dict(overlay)
        else:
            self._overlay = dict()

    def __reduce__(self):
        return (self.__class__, (self.start, len(self), self.perms, self._filename, self._offset, self._overlay))

    def __del__(self):
        _munmap(self._data, self._mapped_size)

    def __repr__(self):
        return '<%s [%s+%x] 0x%016x-0x%016x %s>' % (self.__class__.__name__, self._filename, self._offset, self.start, self.end, self.perms)

    def __setitem__(self, index, value):
        assert not isinstance(index, slice) or \
            len(value) == index.stop - index.start
        index = self._get_offset(index)
        if isinstance(index, slice):
            for i in xrange(index.stop - index.start):
                self._overlay[index.start + i] = value[i]
        else:
            self._overlay[index] = value

    def __getitem__(self, index):
        def get_byte_at_offset(offset):
            if offset in self._overlay:
                return self._overlay[offset]
            else:
                if offset >= self._mapped_size:
                    return '\x00'  # , 'Extra data must initially be zero'
                return self._data[offset]

        index = self._get_offset(index)
        if isinstance(index, slice):
            result = []
            for i in xrange(index.stop - index.start):
                result.append(get_byte_at_offset(i + index.start))
            return result
        else:
            return get_byte_at_offset(index)

    def split(self, address):
        if address <= self.start:
            return None, self
        if address >= self.end:
            return self, None

        assert address > self.start and address <= self.end
        head = COWMap(self, size=address - self.start)
        tail = COWMap(self, offset=address - self.start)
        return head, tail


class COWMap(Map):
    '''
    Copy-on-write based map.
    '''

    def __init__(self, parent, offset=0, perms=None, size=None, **kwargs):
        '''
        A copy on write copy of parent. Writes to the parent after a copy on
        write are unspecified.

        :param parent: the parent map.
        :param offset: an offset within the parent map from where to create the new map.
        :param perms: Permissions on new mapping, or None if inheriting.
        :param size: the size of the new map or max.
        '''
        assert isinstance(parent, Map)
        assert offset >= 0 and offset < len(parent)
        if size is None:
            size = len(parent) - offset
        assert parent.start + offset + size <= parent.end
        if perms is None:
            perms = parent.perms

        super(COWMap, self).__init__(parent.start + offset, size, perms, **kwargs)
        self._parent = parent
        self._parent.__setitem__ = False
        self._cow = {}

    def __setitem__(self, index, value):
        assert self._in_range(index)
        if isinstance(index, slice):
            for i in xrange(index.stop - index.start):
                self._cow[index.start + i] = value[i]
        else:
            self._cow[index] = value

    def __getitem__(self, index):
        assert self._in_range(index)

        if isinstance(index, slice):
            result = []
            for i in xrange(index.start, index.stop):
                if i in self._cow:
                    result.append(self._cow[i])
                else:
                    result.append(self._parent[i])
            return result
        else:
            if index in self._cow:
                return self._cow[index]
            else:
                return self._parent[index]

    def split(self, address):
        if address <= self.start:
            return None, self
        if address >= self.end:
            return self, None

        assert address > self.start and address < self.end
        head = COWMap(self, size=address - self.start)
        tail = COWMap(self, offset=address - self.start)
        return head, tail


class Memory(object):
    __metaclass__ = ABCMeta

    '''
    The memory manager.
    This class handles all virtual memory mappings and symbolic chunks.
    '''

    def __init__(self, maps=None):
        '''
        Builds a memory manager.
        '''
        super(Memory, self).__init__()
        if maps is None:
            self._maps = set()
        else:
            self._maps = set(maps)
        self._page2map = WeakValueDictionary()  # {page -> ref{MAP}}
        self._recording_stack = []
        for m in self._maps:
            for i in range(self._page(m.start), self._page(m.end)):
                assert i not in self._page2map
                self._page2map[i] = m

    def __reduce__(self):
        return (self.__class__, (self._maps, ))

    @abstractproperty
    def memory_bit_size(self):
        return 32

    @abstractproperty
    def page_bit_size(self):
        return 12

    @property
    def memory_size(self):
        return 1 << self.memory_bit_size

    @property
    def page_size(self):
        return 1 << self.page_bit_size

    @property
    def memory_mask(self):
        return self.memory_size - 1

    @property
    def page_mask(self):
        return self.page_size - 1

    @property
    def maps(self):
        return self._maps

    def _ceil(self, address):
        '''
        Returns the smallest page boundary value not less than the address.
        :rtype: int
        :param address: the address to calculate its ceil.
        :return: the ceil of C{address}.
        '''
        return (((address - 1) + self.page_size) & ~self.page_mask) & self.memory_mask

    def _floor(self, address):
        '''
        Returns largest page boundary value not greater than the address.

        :param address: the address to calculate its floor.
        :return: the floor of C{address}.
        :rtype: int
        '''
        return address & ~self.page_mask

    def _page(self, address):
        '''
        Calculates the page number of an address.

        :param address: the address to calculate its page number.
        :return: the page number of address.
        :rtype: int
        '''
        return address >> self.page_bit_size

    def _search(self, size, start=None, counter=0):
        '''
        Recursively searches the address space for enough free space to allocate C{size} bytes.

        :param size: the size in bytes to allocate.
        :param start: an address from where to start the search.
        :param counter: internal parameter to know if all the memory was already scanned.
        :return: the address of an available space to map C{size} bytes.
        :raises MemoryException: if there is no space available to allocate the desired memory.
        :rtype: int


        todo: Document what happens when you try to allocate something that goes round the address 32/64 bit representation.
        '''
        assert size & self.page_mask == 0
        if start is None:
            end = {32: 0xf8000000, 64: 0x0000800000000000}[self.memory_bit_size]
            start = end - size
        else:
            if start > self.memory_size - size:
                start = self.memory_size - size
            end = start + size

        consecutive_free = 0
        for p in xrange(self._page(end - 1), -1, -1):
            if p not in self._page2map:
                consecutive_free += 0x1000
            else:
                consecutive_free = 0
            if consecutive_free >= size:
                return p << self.page_bit_size
            counter += 1
            if counter >= self.memory_size / self.page_size:
                raise MemoryException('Not enough memory')

        return self._search(size, self.memory_size - size, counter)

    def mmapFile(self, addr, size, perms, filename, offset=0):
        '''
        Creates a new file mapping in the memory address space.

        :param addr: the starting address (took as hint). If C{addr} is C{0} the first big enough
                     chunk of memory will be selected as starting address.
        :param size: the contents of a file mapping are initialized using C{size} bytes starting
                     at offset C{offset} in the file C{filename}.
        :param perms: the access permissions to this memory.
        :param filename: the pathname to the file to map.
        :param offset: the contents of a file mapping are initialized using C{size} bytes starting
                      at offset C{offset} in the file C{filename}.
        :return: the starting address where the file was mapped.
        :rtype: int
        :raises error:
                   - 'Address shall be concrete' if C{addr} is not an integer number.
                   - 'Address too big' if C{addr} goes beyond the limit of the memory.
                   - 'Map already used' if the piece of memory starting in C{addr} and with length C{size} isn't free.
        '''
        # If addr is NULL, the system determines where to allocate the region.
        assert addr is None or isinstance(addr, (int, long)), 'Address shall be concrete'
        assert addr < self.memory_size, 'Address too big'
        assert size > 0

        # address is rounded down to the nearest multiple of the allocation granularity
        if addr is not None:
            addr = self._floor(addr)

        # size value is rounded up to the next page boundary
        size = self._ceil(size)

        # If zero search for a spot
        addr = self._search(size, addr)

        # It should not be allocated
        for i in xrange(self._page(addr), self._page(addr + size)):
            assert i not in self._page2map, 'Map already used'

        # Create the map
        m = FileMap(addr, size, perms, filename, offset)

        # Okay, ready to alloc
        self._add(m)

        logger.debug('New file-memory map @%x size:%x', addr, size)
        return addr

    def mmap(self, addr, size, perms, data_init=None, name=None):
        '''
        Creates a new mapping in the memory address space.

        :param addr: the starting address (took as hint). If C{addr} is C{0} the first big enough
                     chunk of memory will be selected as starting address.
        :param size: the length of the mapping.
        :param perms: the access permissions to this memory.
        :param data_init: optional data to initialize this memory.
        :param name: optional name to give to this mapping
        :return: the starting address where the memory was mapped.
        :raises error:
                   - 'Address shall be concrete' if C{addr} is not an integer number.
                   - 'Address too big' if C{addr} goes beyond the limit of the memory.
                   - 'Map already used' if the piece of memory starting in C{addr} and with length C{size} isn't free.
        :rtype: int

        '''
        # If addr is NULL, the system determines where to allocate the region.
        assert addr is None or type(addr) in [int, long], 'Address shall be concrete'
        assert addr < self.memory_size, 'Address too big'

        # address is rounded down to the nearest multiple of the allocation granularity
        if addr is not None:
            addr = self._floor(addr)

        # size value is rounded up to the next page boundary
        size = self._ceil(size)

        # If zero search for a spot
        addr = self._search(size, addr)

        # It should not be allocated
        for i in xrange(self._page(addr), self._page(addr + size)):
            assert i not in self._page2map, 'Map already used'

        # Create the anonymous map
        m = AnonMap(start=addr, size=size, perms=perms, data_init=data_init)

        # Okay, ready to alloc
        self._add(m)

        logger.debug('New memory map @%x size:%x', addr, size)
        return addr

    def _add(self, m):
        assert isinstance(m, Map)
        assert m not in self._maps
        assert m.start & self.page_mask == 0
        assert m.end & self.page_mask == 0
        self._maps.add(m)
        # updating the page to map translation
        for i in range(self._page(m.start), self._page(m.end)):
            self._page2map[i] = m

    def _del(self, m):
        assert isinstance(m, Map)
        assert m in self._maps
        # remove m pages from the page2maps..
        for p in xrange(self._page(m.start), self._page(m.end)):
            del self._page2map[p]
        # remove m from the maps set
        self._maps.remove(m)

    def map_containing(self, address):
        '''
        Returns the L{MMap} object containing the address.

        :param address: the address to obtain its mapping.
        :rtype: L{MMap}

        @todo: symbolic address
        '''
        page_offset = self._page(address)
        if page_offset not in self._page2map:
            raise MemoryException("Page not mapped", address)
        return self._page2map[page_offset]

    def mappings(self):
        '''
        Returns a sorted list of all the mappings for this memory.

        :return: a list of mappings.
        :rtype: list
        '''
        result = []
        for m in self.maps:
            if isinstance(m, AnonMap):
                result.append((m.start, m.end, m.perms, 0, ''))
            elif isinstance(m, FileMap):
                result.append((m.start, m.end, m.perms, m._offset, m._filename))
            else:
                result.append((m.start, m.end, m.perms, 0, m.name))

        return sorted(result)

    def __str__(self):
        return '\n'.join(['%016x-%016x % 4s %08x %s' % (start, end, p, offset, name or '') for start, end, p, offset, name in self.mappings()])

    def _maps_in_range(self, start, end):
        '''
        Generates the list of maps that overlaps with the range [start:end]
        '''

        # Search for the first matching map
        addr = start
        while addr < end:
            if addr not in self:
                addr += self.page_size
            else:
                m = self._page2map[self._page(addr)]
                yield m
                addr = m.end

    def munmap(self, start, size):
        '''
        Deletes the mappings for the specified address range and causes further
        references to addresses within the range to generate invalid memory
        references.

        :param start: the starting address to delete.
        :param size: the length of the unmapping.
        '''
        start = self._floor(start)
        end = self._ceil(start + size)

        for m in self._maps_in_range(start, end):
            self._del(m)
            head, tail = m.split(start)
            middle, tail = tail.split(end)
            assert middle is not None
            if head:
                self._add(head)
            if tail:
                self._add(tail)

        logger.debug('Unmap memory @%x size:%x', start, size)

    def mprotect(self, start, size, perms):
        assert size > 0
        start = self._floor(start)
        end = self._ceil(start + size)

        for m in self._maps_in_range(start, end):
            self._del(m)

            head, tail = m.split(start)
            middle, tail = tail.split(end)

            assert middle is not None
            middle.perms = perms
            self._add(middle)

            if head:
                self._add(head)
            if tail:
                self._add(tail)

    # Permissions
    def __contains__(self, address):
        return self._page(address) in self._page2map

    def perms(self, index):
        # not happy with this interface.
        if isinstance(index, slice):
            # get the more restrictive set of perms for the range
            raise NotImplementedError('No perms for slices')
        else:
            return self.map_containing(index).perms

    def access_ok(self, index, access, force=False):
        if isinstance(index, slice):
            assert index.stop - index.start >= 0
            addr = index.start
            while addr < index.stop:
                if addr not in self:
                    return False
                m = self.map_containing(addr)

                if not force and not m.access_ok(access):
                    return False

                until_next_page = min(m.end - addr, index.stop - addr)
                addr += until_next_page
            assert addr == index.stop
            return True
        else:
            if index not in self:
                return False
            m = self.map_containing(index)
            return force or m.access_ok(access)

    # write and read potentially symbolic bytes at symbolic indexes
    def read(self, addr, size, force=False):
        if not self.access_ok(slice(addr, addr + size), 'r', force):
            raise InvalidMemoryAccess(addr, 'r')

        assert size > 0
        result = []
        stop = addr + size
        p = addr
        while p < stop:
            m = self.map_containing(p)

            _size = min(m.end - p, stop - p)
            result += m[p:p + _size]
            p += _size
        assert p == stop

        return result

    def push_record_writes(self):
        '''
        Begin recording all writes. Retrieve all writes with `pop_record_writes()`
        '''
        self._recording_stack.append([])

    def pop_record_writes(self):
        '''
        Stop recording trace and return a `list[(address, value)]` of all the writes
        that occurred, where `value` is of type list[str]. Can be called without
        intermediate `pop_record_writes()`.

        For example::

            mem.push_record_writes()
                mem.write(1, 'a')
                mem.push_record_writes()
                    mem.write(2, 'b')
                mem.pop_record_writes()  # Will return [(2, 'b')]
            mem.pop_record_writes()  # Will return [(1, 'a'), (2, 'b')]

        Multiple writes to the same address will all be included in the trace in the
        same order they occurred.

        :return: list[tuple]
        '''

        lst = self._recording_stack.pop()
        # Append the current list to a previously-started trace.
        if self._recording_stack:
            self._recording_stack[-1].extend(lst)
        return lst

    def write(self, addr, buf, force=False):
        size = len(buf)
        if not self.access_ok(slice(addr, addr + size), 'w', force):
            raise InvalidMemoryAccess(addr, 'w')
        assert size > 0
        stop = addr + size
        start = addr

        if self._recording_stack:
            self._recording_stack[-1].append((addr, buf))

        while addr < stop:
            m = self.map_containing(addr)
            size = min(m.end - addr, stop - addr)
            m[addr:addr + size] = buf[addr - start:addr - start + size]
            addr += size
        assert addr == stop

    def _get_size(self, size):
        return size

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            size = self._get_size(index.stop - index.start)
            assert len(value) == size  # raise proper Error?
            self.write(index.start, value)
        else:
            self.write(index, (value,))

    def __getitem__(self, index):
        if isinstance(index, slice):
            result = self.read(index.start, index.stop - index.start)
        else:
            result = self.read(index, 1)[0]
        return result


class SMemory(Memory):
    '''
    The symbolic memory manager.
    This class handles all virtual memory mappings and symbolic chunks.

    :todo: improve comments
    '''

    def __init__(self, constraints, symbols=None, *args, **kwargs):
        '''
        Builds a memory.

        :param constraints:  a set of constraints
        :param symbols: Symbolic chunks
        '''
        super(SMemory, self).__init__(*args, **kwargs)
        assert isinstance(constraints, ConstraintSet)
        self._constraints = constraints
        if symbols is None:
            self._symbols = {}
        else:
            self._symbols = dict(symbols)

    def __reduce__(self):
        return (self.__class__, (self.constraints, self._symbols, self._maps, ))

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints

    def _get_size(self, size):
        if isinstance(size, BitVec):
            size = arithmetic_simplify(size)
        else:
            size = BitVecConstant(self.memory_bit_size, size)
        assert isinstance(size, BitVecConstant)
        return size.value

    def munmap(self, start, size):
        '''
        Deletes the mappings for the specified address range and causes further
        references to addresses within the range to generate invalid memory
        references.

        :param start: the starting address to delete.
        :param size: the length of the unmapping.
        '''
        for addr in xrange(start, start + size):
            if addr in self._symbols:
                del self._symbols[addr]
        super(SMemory, self).munmap(start, size)

    def read(self, address, size, force=False):
        '''
        Read a stream of potentially symbolic bytes from a potentially symbolic
        address

        :param address: Where to read from
        :param size: How many bytes
        :param force: Whether to ignore permissions
        :rtype: list
        '''
        size = self._get_size(size)
        assert not issymbolic(size)

        if issymbolic(address):
            assert solver.check(self.constraints)
            logger.debug('Reading %d bytes from symbolic address %s', size, address)
            try:
                solutions = self._try_get_solutions(address, size, 'r', force=force)
                assert len(solutions) > 0
            except TooManySolutions as e:
                m, M = solver.minmax(self.constraints, address)
                logger.debug('Got TooManySolutions on a symbolic read. Range [%x, %x]. Not crashing!', m, M)

                # The force param shouldn't affect this, as this is checking for unmapped reads, not bad perms
                crashing_condition = True
                for start, end, perms, offset, name in self.mappings():
                    if start <= M + size and end >= m:
                        if 'r' in perms:
                            crashing_condition = Operators.AND(Operators.OR((address + size).ult(start), address.uge(end)), crashing_condition)

                if solver.can_be_true(self.constraints, crashing_condition):
                    raise InvalidSymbolicMemoryAccess(address, 'r', size, crashing_condition)

                # INCOMPLETE Result! We could also fork once for every map
                logger.info('INCOMPLETE Result! Using the sampled solutions we have as result')
                condition = False
                for base in e.solutions:
                    condition = Operators.OR(address == base, condition)
                from .state import ForkState
                raise ForkState("Forking state on incomplete result", condition)

            # So here we have all potential solutions to address

            condition = False
            for base in solutions:
                condition = Operators.OR(address == base, condition)

            result = []
            # consider size ==1 to read following code
            for offset in range(size):
                # Given ALL solutions for the symbolic address
                for base in solutions:
                    addr_value = base + offset
                    byte = Operators.ORD(self.map_containing(addr_value)[addr_value])
                    if addr_value in self._symbols:
                        for condition, value in self._symbols[addr_value]:
                            byte = Operators.ITEBV(8, condition, Operators.ORD(value), byte)
                    if len(result) > offset:
                        result[offset] = Operators.ITEBV(8, address == base, byte, result[offset])
                    else:
                        result.append(byte)
                    assert len(result) == offset + 1
            return map(Operators.CHR, result)
        else:
            result = map(Operators.ORD, super(SMemory, self).read(address, size, force))
            for offset in range(size):
                if address + offset in self._symbols:
                    for condition, value in self._symbols[address + offset]:
                        if condition is True:
                            result[offset] = Operators.ORD(value)
                        else:
                            result[offset] = Operators.ITEBV(8, condition, Operators.ORD(value), result[offset])
            return map(Operators.CHR, result)

    def write(self, address, value, force=False):
        '''
        Write a value at address.
        :param address: The address at which to write
        :type address: int or long or Expression
        :param value: Bytes to write
        :type value: str or list
        :param force: Whether to ignore permissions
        '''
        size = len(value)
        if issymbolic(address):

            solutions = self._try_get_solutions(address, size, 'w', force=force)

            for offset in xrange(size):
                for base in solutions:
                    condition = base == address
                    self._symbols.setdefault(base + offset, []).append((condition, value[offset]))
        else:

            for offset in xrange(size):
                if issymbolic(value[offset]):
                    if not self.access_ok(address + offset, 'w', force):
                        raise InvalidMemoryAccess(address + offset, 'w')
                    self._symbols[address + offset] = [(True, value[offset])]
                else:
                    # overwrite all previous items
                    if address + offset in self._symbols:
                        del self._symbols[address + offset]
                    super(SMemory, self).write(address + offset, [value[offset]], force)

    def _try_get_solutions(self, address, size, access, max_solutions=0x1000, force=False):
        '''
        Try to solve for a symbolic address, checking permissions when reading/writing size bytes.

        :param Expression address: The address to solve for
        :param int size: How many bytes to check permissions for
        :param str access: 'r' or 'w'
        :param int max_solutions: Will raise if more solutions are found
        :param force: Whether to ignore permission failure
        :rtype: list
        '''
        assert issymbolic(address)

        solutions = solver.get_all_values(self.constraints, address, maxcnt=max_solutions)

        crashing_condition = False
        for base in solutions:
            if not self.access_ok(slice(base, base + size), access, force):
                crashing_condition = Operators.OR(address == base, crashing_condition)

        if solver.can_be_true(self.constraints, crashing_condition):
            raise InvalidSymbolicMemoryAccess(address, access, size, crashing_condition)

        return solutions


class Memory32(Memory):
    memory_bit_size = 32
    page_bit_size = 12


class Memory64(Memory):
    memory_bit_size = 64
    page_bit_size = 12


class SMemory32(SMemory):
    memory_bit_size = 32
    page_bit_size = 12


class SMemory32L(SMemory):
    memory_bit_size = 32
    page_bit_size = 13


class SMemory64(SMemory):
    memory_bit_size = 64
    page_bit_size = 12
