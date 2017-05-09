from cStringIO import StringIO
from manticore.core.smtlib import Solver, Operators
import unittest
import tempfile, os
import gc, pickle
import fcntl
import resource
from manticore.core.memory import *

def issymbolic(value):
    return isinstance(value, Expression)

def isconcrete(value):
    return not issymbolic(value)


class MemoryTest(unittest.TestCase):
    def get_open_fds(self):
        fds = []
        for fd in range(3, resource.RLIMIT_NOFILE):
            try:
                flags = fcntl.fcntl(fd, fcntl.F_GETFD)
            except IOError:
                continue
            fds.append(fd)
        return fds

    def setUp(self):
        import sys
        sys.setrecursionlimit(10000)
        solver._stop_proc()
        self.fds = self.get_open_fds()
    def tearDown(self):
        solver._stop_proc()
        gc.collect()
        gc.garbage = []
        gc.collect()
        self.assertEqual(self.fds, self.get_open_fds())

    def test_ceil_floor_page_memory_page_12(self):
        mem = Memory32()
        #Basic check ceil
        self.assertEqual(0x12346000, mem._ceil(0x12345678))
        self.assertEqual(0x12346000, mem._ceil(0x12346000))
        self.assertEqual(0x00000000, mem._ceil(0xffffffff))
        #Basic check floor
        self.assertEqual(0x12345000, mem._floor(0x12345678))
        self.assertEqual(0x12345000, mem._floor(0x12345000))
        self.assertEqual(0xfffff000, mem._floor(0xffffffff))
        #Basic check page
        self.assertEqual(0x12345, mem._page(0x12345678))
        self.assertEqual(0x12345, mem._page(0x12345000))
        self.assertEqual(0xfffff, mem._page(0xffffffff))

    def test_ceil_floor_page_memory_page_13(self):
        mem = SMemory32L(ConstraintSet())
        self.assertEqual(0x00002000, mem._ceil(0x00002000))
        self.assertEqual(0x00002000, mem._floor(0x00002000))
        self.assertEqual(0x00000001, mem._page(0x00003FFF))

        self.assertEqual(0xABC0E000, mem._ceil(0xABC0D590))
        self.assertEqual(0xABC0C000, mem._floor(0xABC0D590))
        self.assertEqual(0x55E06, mem._page(0xABC0D590))

    def test_search_and_mmap_several_chunks_memory_page_12(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #Check the search gives any value as the mem is free
        self.assertEqual(mem._search(0x1000, 0x20000000), 0x20000000)
        #Check the search still gives any value as the mem is still free
        self.assertEqual(mem._search(0x1000, 0xf0000000), 0xf0000000)

        #Check the default initial value
        self.assertEqual(mem._search(0x1000, None), 0xf7fff000)

       
        #alloc/map a byte at default address.
        first = mem.mmap(None, 0x0001, 'r')
        self.assertEqual(first, 0xf7fff000)

        #Okay 2 maps
        self.assertEqual(len(mem.mappings()), 1)
        #check valid 
        self.assertTrue(first in mem)
        self.assertTrue(mem.access_ok((first), 'r'))
        self.assertFalse(isinstance(mem[first], Expression))
        self.assertTrue(first+0x1000-1 in mem)
        self.assertTrue(mem.access_ok((first+0x1000-1), 'r'))
        self.assertFalse(isinstance(mem[first+0x1000-1], Expression))
        #bytes outside the map should be not valid
        self.assertFalse(first-1 in mem)
        self.assertFalse(first+0x1000 in mem)


        #alloc/map another map. Should be consecutive to the lower address
        second = mem.mmap(None, 0x1000, 'w')
        #Okay 2 maps
        self.assertEqual(len(mem.mappings()), 2)
        #check valid 
        self.assertTrue(second in mem)
        self.assertTrue(mem.access_ok((second), 'w'))
        self.assertTrue(second+0x1000-1 in mem)
        self.assertTrue(mem.access_ok((second+0x1000-1), 'w'))
        #bytes outside the map should be not valid
        self.assertFalse(second-1 in mem)
        self.assertFalse(first+0x1000 in mem)
                    
        #alloc/map a byte
        third = mem.mmap(None, 0x1000, 'x')
        
        #Okay 3 maps
        self.assertEqual(len(mem.mappings()), 3)

        self.assertTrue(first in mem)
        self.assertTrue(mem.access_ok((first), 'r'))

        self.assertTrue(second in mem)
        self.assertTrue(mem.access_ok((second), 'w'))

        self.assertTrue(third in mem)
        self.assertTrue(mem.access_ok((third), 'x'))

        self.assertFalse(third-1 in mem)
        self.assertFalse(first+0x1000 in mem)

        self.assertFalse(mem.access_ok((second), 'x'))
        mem.munmap(second,1) 
        self.assertFalse(second in mem)
        self.assertEqual(len(mem.mappings()), 2)

        #---------alloc in the free spaces now!----------------
        forth = mem.mmap(second, 0x1000, 'x')
        self.assertEqual(forth, mem._ceil(third+1))
        self.assertTrue(forth in mem)
        self.assertTrue(mem.access_ok((forth), 'x'))
        
    def test_search_and_mmap_several_chunks_testing_limits_memory_page_12(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #Check the search gives basically any value as the mem is free
        self.assertEqual(mem._search(0x1000, 0x20000000), 0x20000000)

        #alloc/map a byte
        first = mem.mmap(0xFFFF000, 0x0001, 'r')
        zero  = mem.mmap(0x000, 0x0001, 'w')

        #Okay 2 map
        self.assertEqual(len(mem.mappings()), 2)

        self.assertTrue(first in mem)
        self.assertTrue(mem.access_ok((first), 'r'))
        #self.assertFalse(mem.has_symbols(first))

        self.assertTrue(zero in mem)
        self.assertRaises(AssertionError, mem.mmap, 0x0000F000, 0, 'r')
        
        self.assertEqual(zero, 0)

    def test_try_to_allocate_greater_than_last_space_memory_page_12(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #alloc/map a byte
        for i in range(16):
            mem.mmap( i<< 28, 0x1000, 'r')
        self.assertEqual(len(mem.mappings()), 16)
        self.assertRaises(MemoryException, mem.mmap, None, 0x10000000, 'r')

        self.assertEqual(len(mem.mappings()), 16)


    def test_access_symbolic_r(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        sym = cs.new_bitvec(32)
        val = cs.new_bitvec(8)

        cs.add(sym.uge(0xfff))
        cs.add(sym.ule(0x1010))

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        self.assertRaises(MemoryException, mem.__getitem__, 0x1000)
        self.assertRaises(MemoryException, mem.__getitem__, sym)
        self.assertRaises(MemoryException, mem.__setitem__, 0x1000, '\x42')
        self.assertRaises(MemoryException, mem.__setitem__, sym, '\x42')


        #alloc/map a byte
        first = mem.mmap(0x1000, 0x1000, 'r')


        self.assertEqual(first, 0x1000)
        self.assertEqual(mem[0x1000], '\x00')
        self.assertRaises(MemoryException, mem.__getitem__, sym)
        self.assertRaises(MemoryException, mem.__setitem__, 0x1000, '\x41')
        self.assertRaises(MemoryException, mem.__setitem__, 0x1000, val)
        self.assertRaises(MemoryException, mem.__setitem__, sym, '\x41')
        self.assertRaises(MemoryException, mem.__setitem__, sym, val)


    def test_access_symbolic_w(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        sym = cs.new_bitvec(32)
        val = cs.new_bitvec(8)

        cs.add(sym.uge(0xfff))
        cs.add(sym.ule(0x1010))

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)
        self.assertRaises(MemoryException, mem.__getitem__, 0x1000)
        self.assertRaises(MemoryException, mem.__getitem__, sym)


        self.assertRaises(MemoryException, mem.__setitem__, 0x1000, '\x41')
        self.assertRaises(MemoryException, mem.__setitem__, sym, '\x41')
        
        #alloc/map a byte
        first = mem.mmap(0x1000, 0x1000, 'w')

        self.assertEqual(first, 0x1000)
        self.assertRaises(MemoryException, mem.__getitem__, 0x1000)
        self.assertRaises(MemoryException, mem.__getitem__, sym)
        mem[0x1000] = '\x40'
        mem[0x1000] = val
        self.assertRaises(MemoryException, mem.__setitem__, sym, '\x41')
        self.assertRaises(MemoryException, mem.__setitem__, sym, val)

        cs.add( sym.uge(0x1000))
  
        mem[sym] = '\x40'
        mem[sym] = val

    def test_access(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #alloc/map a byte
        first = mem.mmap(0x1000, 0x1000, 'r')
        second  = mem.mmap(0x2000, 0x1000, 'w')
        third  = mem.mmap(0x3000, 0x1000, 'x')

        #Okay 3 maps
        self.assertEqual(len(mem.mappings()), 3)
        self.assertItemsEqual((first,second,third), (0x1000,0x2000,0x3000))

        #not mapped implies no access
        self.assertFalse(mem.access_ok(first-1, 'r'))
        self.assertFalse(mem.access_ok(first-1, 'w'))
        self.assertFalse(mem.access_ok(first-1, 'x'))
        self.assertFalse(mem.access_ok(third+0x1000+1, 'r'))
        self.assertFalse(mem.access_ok(third+0x1000+1, 'w'))
        self.assertFalse(mem.access_ok(third+0x1000+1, 'x'))

        #expected access
        self.assertTrue(mem.access_ok(first, 'r'))
        self.assertTrue(mem.access_ok(second, 'w'))
        self.assertTrue(mem.access_ok(third, 'x'))

        #unexpected access single
        self.assertFalse(mem.access_ok(first, 'w'))
        self.assertFalse(mem.access_ok(second, 'x'))
        self.assertFalse(mem.access_ok(third, 'r'))
        self.assertFalse(mem.access_ok(first, 'x'))
        self.assertFalse(mem.access_ok(second, 'r'))
        self.assertFalse(mem.access_ok(third, 'w'))

        #unexpected access double
        self.assertFalse(mem.access_ok(first, 'rw'))
        self.assertFalse(mem.access_ok(second, 'wx'))
        self.assertFalse(mem.access_ok(third, 'rx'))
        self.assertFalse(mem.access_ok(first, 'wx'))
        self.assertFalse(mem.access_ok(second, 'rx'))
        self.assertFalse(mem.access_ok(third, 'rw'))

        #unexpected access triple
        self.assertFalse(mem.access_ok(first, 'rwx'))
        self.assertFalse(mem.access_ok(second, 'rwx'))
        self.assertFalse(mem.access_ok(third, 'rwx'))

        #Map slices
        self.assertTrue(mem.access_ok(slice(first,first+0x1000), 'r'))
        self.assertFalse(mem.access_ok(slice(first,first+0x1000), 'w'))
        self.assertFalse(mem.access_ok(slice(first,first+0x1000), 'x'))
        self.assertFalse(mem.access_ok(slice(second,second+0x1000), 'r'))
        self.assertTrue(mem.access_ok(slice(second,second+0x1000), 'w'))
        self.assertFalse(mem.access_ok(slice(second,second+0x1000), 'x'))
        self.assertFalse(mem.access_ok(slice(third,third+0x1000), 'r'))
        self.assertFalse(mem.access_ok(slice(third,third+0x1000), 'w'))
        self.assertTrue(mem.access_ok(slice(third,third+0x1000), 'x'))

        #All 3 maps
        self.assertFalse(mem.access_ok(slice(first,third+0x1000), 'r'))
        self.assertFalse(mem.access_ok(slice(first,third+0x1000), 'w'))
        self.assertFalse(mem.access_ok(slice(first,third+0x1000), 'x'))


        self.assertFalse(mem.access_ok(slice(first-1,first+0x1000), 'r'))
        self.assertFalse(mem.access_ok(slice(first,first+0x1001), 'r'))
        self.assertFalse(mem.access_ok(slice(second-1,second+0x1000), 'r'))
        self.assertFalse(mem.access_ok(slice(second,second+0x1001), 'r'))
        self.assertFalse(mem.access_ok(slice(third-1,third+0x1000), 'r'))
        self.assertFalse(mem.access_ok(slice(third,third+0x1001), 'r'))



    def test_not_enough_memory_page_12(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #alloc/map a chunk
        first = mem.mmap((0x100000000/2), 0x1000, 'r')

        #Okay 2 map
        self.assertEqual(len(mem.mappings()), 1)

        self.assertTrue(first in mem)
        self.assertTrue(mem.access_ok((first), 'r'))

        self.assertRaises(MemoryException, mem.mmap, 0, (0x100000000/2)+1, 'r')

    def testBasicAnonMap(self):
        m = AnonMap(0x10000000, 0x2000, 'rwx')
        
        #Check the size
        self.assertEqual(len(m), 0x2000)


        #check the outside limits
        self.assertRaises(IndexError, m.__setitem__, 0x10000000-1, 'A')
        self.assertRaises(IndexError, m.__setitem__, 0x10002000, 'A')
        self.assertRaises(IndexError, m.__getitem__, 0x10000000-1)
        self.assertRaises(IndexError, m.__getitem__, 0x10002000)


        #check it is initialized with zero
        self.assertEqual(m[0x10000000], Operators.CHR(0))
        self.assertEqual(m[0x10002000-1], Operators.CHR(0))


        #check all characters go and come back the same...
        #at the first byte of the mapping
        addr = 0x10000000
        for c in xrange(0, 0x100):
            m[addr] = Operators.CHR(c)
            self.assertEqual(m[addr], Operators.CHR(c))

        #at the last byte of the mapping
        addr = 0x10002000-1
        for c in xrange(0, 0x100):
            m[addr] = Operators.CHR(c)
            self.assertEqual(m[addr], Operators.CHR(c))


    def test_basic_get_char(self):
        mem = SMemory32(ConstraintSet())
        addr = mem.mmap(None, 0x10, 'rw')
        mem[addr] = 'a' 

        mem[addr+0x10:addr+0x20] = 'Y'*0x10
        self.assertItemsEqual(mem[addr+0x10-1:addr+0x20+1], '\x00' + 'Y'*0x10 +'\x00')


    def test_basic_put_char_get_char(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)
        
        #alloc/map a litlle mem
        addr = mem.mmap(None, 0x10, 'r')
        for c in xrange(0, 0x10):
            self.assertRaises(MemoryException, mem.__setitem__, addr+c, 'a')

        addr = mem.mmap(None, 0x10, 'x')
        for c in xrange(0, 0x10):
            self.assertRaises(MemoryException, mem.__setitem__, addr+c, 'a')

        addr = mem.mmap(None, 0x10, 'w')
        for c in xrange(0, 0x10):
            mem[addr+c] = 'a'

        for c in xrange(0, 0x10):
            self.assertRaises(MemoryException, mem.__getitem__, addr+c)

        addr = mem.mmap(None, 0x10, 'wx')
        for c in xrange(0, 0x10):
            mem[addr+c] = 'a'
        for c in xrange(0, 0x10):
            self.assertRaises(MemoryException, mem.__getitem__, addr+c)

        addr = mem.mmap(None, 0x10, 'rw')
        for c in xrange(0, 0x10):
            mem[addr+c] = 'a'
        for c in xrange(0, 0x10):
            self.assertEquals(mem[addr+c], 'a')

    def testBasicMappingsLimits(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #Check the search gives basically any value as the mem is free
        self.assertEqual(mem._search(0x1000, 0x20000000), 0x20000000)

        #alloc/map a litlle mem
        size = 0x1000
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 map
        self.assertEqual(len(mem.mappings()), 1)

        #positive tests
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)

        for i in xrange(addr, addr+size):
            self.assertTrue(i in mem)

        #negative tests
        self.assertFalse(0 in mem)
        self.assertFalse(0xffffffff in mem)
        self.assertFalse(-1 in mem)
        self.assertFalse(0xfffffffffffffffffffffffffff in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+0x1000 in mem)

        #check all characters go and come back the same...
        for c in xrange(0, 0x100):
            mem[addr+0x800] = Operators.CHR(c)
            self.assertEqual(mem[addr+0x800], Operators.CHR(c))

    def testBasicMappingsPermissions(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #Chack the search gives basically any value as the mem is free
        self.assertEqual(mem._search(0x1000, 0x20000000), 0x20000000)

        #alloc/map a litlle mem
        size = 0x1000
        addr = mem.mmap(None, 0x1000, 'r')

        #Okay 1 map
        self.assertEqual(len(mem.mappings()), 1)

        #positive tests
        self.assertTrue(addr in mem)
        self.assertFalse(mem.access_ok(addr, 'w'))
        self.assertFalse(mem.access_ok(addr, 'x'))
        self.assertTrue(mem.access_ok(addr, 'r'))
        self.assertFalse(isinstance(mem[addr], Expression))
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(mem.access_ok(addr+size-1, 'w'))
        self.assertFalse(mem.access_ok(addr+size-1, 'x'))
        self.assertTrue(mem.access_ok(addr+size-1, 'r'))
        self.assertTrue(addr-1 not in mem)


        #ad hoc sensible tests
        self.assertFalse(0 in mem)
        self.assertFalse(0xffffffff in mem)
        self.assertFalse(-1 in mem)
        self.assertFalse(0xfffffffffffffffffffffffffff in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(mem.access_ok(addr-1, 'w'))
        self.assertFalse(mem.access_ok(addr-1, 'x'))
        self.assertFalse(mem.access_ok(addr-1, 'r'))
        self.assertFalse(addr+size in mem)
        self.assertFalse(mem.access_ok((addr+size), 'w'))
        self.assertFalse(mem.access_ok((addr+size), 'x'))
        self.assertFalse(mem.access_ok((addr+size), 'r'))


    def testBasicUnmapping(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr, size)

        #Okay 0 maps
        self.assertEqual(len(mem.mappings()), 0)

        #limits
        self.assertFalse(addr in mem)
        self.assertFalse(addr+size-1 in mem)

        #re alloc mem should be at the same address
        addr1 = mem.mmap(addr, size, 'rwx')
        self.assertEqual(addr1, addr)


    def testRoundingToPageUnmapping(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr+0x1000+0x1234, 0x1234)

        '''
        00000000f7ff0000-00000000f7ff2000  rwx 00000000 
        00000000f7ff4000-00000000f8000000  rwx 00000000 
        '''

        #Okay 2 maps
        self.assertEqual(len(mem.mappings()), 2)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+0x1000 in mem)
        self.assertTrue(addr+0x2000-1 in mem)
        self.assertFalse(addr+0x2100 in mem)
        self.assertFalse(addr+0x2001 in mem)
        self.assertFalse(addr+0x2000 in mem)
        self.assertFalse(addr+0x4000-1 in mem)
        self.assertTrue(addr+0x4000 in mem)
        self.assertEqual(str(mem), '00000000f7ff0000-00000000f7ff2000  rwx 00000000 \n00000000f7ff4000-00000000f8000000  rwx 00000000 ')

    def testBasicUnmappingBegginning(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr, size/2)

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertFalse(addr in mem)
        self.assertFalse(addr+size/2-1 in mem)
        self.assertTrue(addr+size/2 in mem)
        self.assertTrue(addr+size-1 in mem)

        #re alloc mem should be at the same address
        addr1 = mem.mmap(addr, size/2, 'rwx')
        self.assertEqual(addr1, addr)

    def testBasicUnmappingEnd(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr+size/2, size)

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size/2-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size/2 in mem)
        self.assertFalse(addr+size-1 in mem)

    def testBasicUnmappingMiddle(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x30000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr+size/3, size/3)

        #Okay 2 maps
        self.assertEqual(len(mem.mappings()), 2)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size/3-1 in mem)
        self.assertTrue(addr+2*size/3 in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size/3 in mem)
        self.assertFalse(addr+2*size/3-1 in mem)
        self.assertFalse(addr+size in mem)

        addr1 = mem.mmap(None, size/3, 'rwx')
        self.assertEqual(addr1, addr+size/3)

    def testBasicUnmapping2(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        #Check the search gives basically any value as the mem is free
        self.assertEqual(mem._search(0x1000, 0x20000000), 0x20000000)

        size = 0x10000
        #alloc/map a little mem
        addr0 = mem.mmap(None, size, 'rwx')
        #alloc/map another little mem
        addr1 = mem.mmap(addr0+size, size, 'rw')

        #They are consecutive
        self.assertEqual(addr0+size, addr1)

        #and 2 maps
        self.assertEqual(len(mem.mappings()), 2)

        #limits
        self.assertTrue(addr0 in mem)
        self.assertTrue(addr0+size-1 in mem)
        self.assertTrue(addr0+1 in mem)
        self.assertTrue(addr1-1 in mem)
        self.assertTrue(addr1 in mem)
        self.assertTrue(addr1+size-1 in mem)
        self.assertFalse(addr0-1 in mem)
        self.assertFalse(addr1+size in mem)

        #Okay unmap a section touching both mappings
        mem.munmap(addr0+size/2, size)
        #Still 2 maps
        self.assertEqual(len(mem.mappings()), 2)

        #limits
        self.assertTrue(addr0 in mem)
        self.assertTrue(addr0 + size/2-1 in mem)
        self.assertTrue(addr1 + size/2 in mem)
        self.assertTrue(addr1 + size-1 in mem)

        self.assertFalse(addr0-1 in mem)
        self.assertFalse((addr0 + size/2) in mem)

        self.assertFalse((addr1+size/2-1) in mem)
        self.assertFalse(addr1+size in mem)
        self.assertFalse(addr1 in mem)


        #re alloc mem should be at the same address
        addr_re = mem.mmap(addr0+size/2, size-0x1000, 'rwx')
        self.assertEqual(addr_re, addr0+size/2)

        #Now 3 maps
        self.assertEqual(len(mem.mappings()), 3)

    def testBasicUnmappingErr(self):
        mem = SMemory32(ConstraintSet())

        size = 0x2000
        #alloc/map a little mem
        addr0 = mem.mmap(None, size, 'rwx')
        #alloc/map another little mem
        addr1 = mem.mmap(addr0+size, size, 'rwx')
        #alloc/map another little mem
        addr2 = mem.mmap(addr1+size, size, 'rwx')

        #They are consecutive
        self.assertEqual(addr0+size, addr1)
        #They are consecutive
        self.assertEqual(addr1+size, addr2)

        #and 2 maps
        self.assertEqual(len(mem.mappings()), 3)

        #Okay unmap a section touching both mappings
        mem.munmap(addr1, size)

        #Still 2 maps
        self.assertEqual(len(mem.mappings()), 2)


    def testBasicUnmappingOverLowerLimit(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(0x10000, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr-size/2, size)
        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr+size/2 in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr in mem)
        self.assertFalse(addr+size/2-1 in mem)

    def testBasicUnmappingOverHigherLimit(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(0x10000, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr+size/2, size)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size/2-1 in mem)
        self.assertFalse(addr+size/2 in mem)
        self.assertFalse(addr+size-1 in mem)

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

    def testUnmappingAll(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr, size/2)

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)
        
        #Okay unmap 
        mem.munmap(addr+size/2, size/2)

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 0)

    def testBasicUnmappingOverBothLimits(self):
        mem = SMemory32(ConstraintSet())

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x30000
        #alloc/map a little mem
        addr = mem.mmap(0x10000, size, 'rwx')

        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size in mem)

        #Okay unmap 
        mem.munmap(addr+size - size/3, size/2)

        #Okay unmap 
        mem.munmap(addr - (size/2 - size/3), size/2)

        #limits
        self.assertTrue((addr+size - size/3 - 1) in mem )
        self.assertFalse((addr+size - size/3) in mem )
        
        self.assertFalse((addr - (size/2 - size/3) + size/2 - 1) in mem )
        self.assertTrue((addr - (size/2 - size/3) + size/2) in mem )
        
        self.assertFalse(addr in mem)
        self.assertFalse(addr+size-1 in mem)
        #Okay 1 maps
        self.assertEqual(len(mem.mappings()), 1)

    def test_mmapFile(self):
        mem = SMemory32(ConstraintSet())
        
        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)
        
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('a'*0x1001)
        rwx_file.close()
        
        addr_a = mem.mmapFile(0, 0x1000, 'rwx', rwx_file.name)

        self.assertEqual(len(mem.mappings()), 1)
        
        self.assertEqual(mem[addr_a], 'a')
        self.assertEqual(mem[addr_a+(0x1000/2)], 'a')
        self.assertEqual(mem[addr_a+(0x1000-1)], 'a')
        self.assertRaises(MemoryException, mem.__getitem__, addr_a+(0x1000))
        
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('b'*0x1001)
        rwx_file.close()
        
        addr_b = mem.mmapFile(0, 0x1000, 'rw', rwx_file.name)

        self.assertEqual(len(mem.mappings()), 2)
        
        self.assertEqual(mem[addr_b], 'b')
        self.assertEqual(mem[addr_b+(0x1000/2)], 'b')
        self.assertEqual(mem[addr_b+(0x1000-1)], 'b')

                                             
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('c'*0x1001)
        rwx_file.close()

        addr_c = mem.mmapFile(0, 0x1000, 'rx', rwx_file.name)

        self.assertEqual(len(mem.mappings()), 3)
        
        self.assertEqual(mem[addr_c], 'c')
        self.assertEqual(mem[addr_c+(0x1000/2)], 'c')
        self.assertEqual(mem[addr_c+(0x1000-1)], 'c')
        
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('d'*0x1001)
        rwx_file.close()
        
        addr_d = mem.mmapFile(0, 0x1000, 'r', rwx_file.name)

        self.assertEqual(len(mem.mappings()), 4)
        
        self.assertEqual(mem[addr_d], 'd')
        self.assertEqual(mem[addr_d+(0x1000/2)], 'd')
        self.assertEqual(mem[addr_d+(0x1000-1)], 'd')
        
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('e'*0x1001)
        rwx_file.close()
        
        addr_e = mem.mmapFile(0, 0x1000, 'w', rwx_file.name)

        self.assertEqual(len(mem.mappings()), 5)
        
        self.assertRaises(MemoryException, mem.__getitem__, addr_e)
        self.assertRaises(MemoryException, mem.__getitem__, addr_e+(0x1000/2))
        self.assertRaises(MemoryException, mem.__getitem__, addr_e+(0x1000-1))

    def test_basic_mapping_with_mmapFile(self):
        mem = SMemory32(ConstraintSet())
        
        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)
        
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('d'*0x1001)
        rwx_file.close()
        addr = mem.mmapFile(0, 0x1000, 'rwx', rwx_file.name)

        #One mapping
        self.assertEqual(len(mem.mappings()), 1)

        for i in xrange(addr, addr+0x1000):
            self.assertTrue(i in mem)
            self.assertTrue(mem.access_ok((i), 'r'))
            self.assertTrue(mem.access_ok((i), 'w'))

        self.assertFalse(addr-1 in mem)
        self.assertFalse(mem.access_ok((addr-1), 'r'))
        self.assertFalse(mem.access_ok((addr-1), 'w'))
        self.assertFalse(addr+0x1000 in mem)
        self.assertFalse(mem.access_ok((addr+0x1000), 'r'))
        self.assertFalse(mem.access_ok((addr+0x1000), 'w'))


        self.assertFalse(mem.access_ok(slice(addr-1,addr+1), 'r'))
        self.assertFalse(mem.access_ok(slice(addr-1,addr+1), 'w'))
        self.assertTrue(mem.access_ok(slice(addr,addr+1), 'rw'))



        self.assertEqual(len(mem.mappings()), 1)
        
        r_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        r_file.file.write('b'*0x1000)
        r_file.close()
        mem.mmapFile(0, 0x1000, 'r', r_file.name)


        #Two mapping
        self.assertEqual(len(mem.mappings()), 2)

        rw_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rw_file.file.write('abcd'* (0x1000/4))
        rw_file.close()
        addr = mem.mmapFile(None, 0x1000, 'rw', rw_file.name)

        self.assertItemsEqual(mem[addr:addr+6],   'abcdab')
        self.assertItemsEqual(mem[addr+1:addr+7], 'bcdabc')
        self.assertItemsEqual(mem[addr+2:addr+8], 'cdabcd')
        self.assertItemsEqual(mem[addr+3:addr+9], 'dabcda')

        #Three mapping
        self.assertEqual(len(mem.mappings()), 3)
        
        size = 0x30000
        w_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        w_file.file.write('abc'*(size/3))
        w_file.close()
        addr = mem.mmapFile(0x20000000, size, 'w', w_file.name)
        
        #Four mapping
        self.assertEqual(len(mem.mappings()), 4)

        #Okay unmap 
        mem.munmap(addr+size/3, size/3)

        #Okay 2 maps
        self.assertEqual(len(mem.mappings()), 5)

        #limits
        self.assertTrue(addr in mem)
        self.assertTrue(addr+size/3-1 in mem)
        self.assertTrue(addr+2*size/3 in mem)
        self.assertTrue(addr+size-1 in mem)
        self.assertFalse(addr-1 in mem)
        self.assertFalse(addr+size/3 in mem)
        self.assertFalse(addr+2*size/3-1 in mem)
        self.assertFalse(addr+size in mem)

        #re alloc mem should be at the same address
        addr1 = mem.mmap(addr, size, 'rwx')
        self.assertTrue(addr1, addr)

        #Delete the temporary file
        os.unlink(rwx_file.name)
        os.unlink(r_file.name)
        os.unlink(w_file.name)


    def test_mix_of_concrete_and_symbolic__push_pop_cleaning_store(self):
        #global mainsolver
        cs = ConstraintSet()
        mem = SMemory32(cs)
        
        start_mapping_addr = mem.mmap(None, 0x1000, 'rwx')
        
        concrete_addr = start_mapping_addr
        symbolic_addr = start_mapping_addr+1
        
        mem[concrete_addr] = 'C'
        sym = cs.new_bitvec(8)
        
        mem[symbolic_addr] = sym
        cs.add(sym.uge(0xfe))
        values = list(solver.get_all_values(cs, sym))
        self.assertIn(0xfe, values)
        self.assertIn(0xff, values)
        self.assertNotIn(0x7f, values)

        self.assertTrue(isinstance(mem[symbolic_addr], Expression))

        values = list(solver.get_all_values(cs, mem[symbolic_addr]))
        self.assertIn(0xfe, values)
        self.assertIn(0xff, values)
        self.assertNotIn(0x7f, values)
                    
        with cs as cs_temp:
            cs_temp.add(sym==0xfe)
            values = list(solver.get_all_values(cs_temp, sym))
            self.assertIn(0xfe, values)
            self.assertNotIn(0xff, values)
            self.assertNotIn(0x7f, values)
            values = list(solver.get_all_values(cs_temp, mem[symbolic_addr]))
            self.assertIn(0xfe, values)
            self.assertNotIn(0xff, values)
            self.assertNotIn(0x7f, values)
        

        values = list(solver.get_all_values(cs, sym))
        self.assertIn(0xfe, values)
        self.assertIn(0xff, values)
        self.assertNotIn(0x7f, values)
        values = list(solver.get_all_values(cs, mem[symbolic_addr]))
        self.assertIn(0xfe, values)
        self.assertIn(0xff, values)
        self.assertNotIn(0x7f, values)

    def test_mix_of_concrete_and_symbolic(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        
        start_mapping_addr = mem.mmap(None, 0x1000, 'rwx')
        
        concretes = [0, 2, 4, 6]
        symbolics = [1, 3, 5, 7]
        
        for range in concretes:
            mem[start_mapping_addr+range] = 'C'
        
        for range in symbolics:
            mem[start_mapping_addr+range] = cs.new_bitvec(8)

        for range in concretes:
            self.assertTrue(isconcrete(mem[start_mapping_addr+range]))

        for range in concretes:
            self.assertFalse(issymbolic(mem[start_mapping_addr+range]))
        
        for range in symbolics:
            self.assertTrue(issymbolic(mem[start_mapping_addr+range]))                

        for range in symbolics:
            self.assertFalse(isconcrete(mem[start_mapping_addr+range]))
    
        for range in symbolics:
            mem[start_mapping_addr+range] = 'C'
        
        for range in concretes:
            mem[start_mapping_addr+range] = cs.new_bitvec(8)

        for range in symbolics:
            self.assertTrue(isconcrete(mem[start_mapping_addr+range]))

        for range in symbolics:
            self.assertFalse(issymbolic(mem[start_mapping_addr+range]))
        
        for range in concretes:
            self.assertTrue(issymbolic(mem[start_mapping_addr+range]))                

        for range in concretes:
            self.assertFalse(isconcrete(mem[start_mapping_addr+range]))

    def test_one_concrete_one_symbolic(self):
        #global mainsolver
        cs = ConstraintSet()
        mem = SMemory32(cs)
        
        addr_for_symbol1 = mem.mmap(None, 0x1000, 'rwx')
        mem[addr_for_symbol1] = 'A'

        symbol1 = cs.new_bitvec(8)
        
        cs.add(Operators.OR(symbol1==Operators.ORD('B'), symbol1==Operators.ORD('C')))

        mem[addr_for_symbol1+1] = symbol1
        
        values = list(solver.get_all_values(cs, symbol1))
        self.assertIn(Operators.ORD('B'), values)
        self.assertIn(Operators.ORD('C'), values)
        
        symbol2 = cs.new_bitvec(32)
        cs.add(symbol2>=addr_for_symbol1)
        cs.add(symbol2<=addr_for_symbol1+1)

        c = mem[symbol2]
        self.assertTrue(issymbolic(c))           
        
        values = list(solver.get_all_values(cs, c))
        
        self.assertIn(Operators.ORD('A'), values)
        self.assertIn(Operators.ORD('B'), values)
        self.assertIn(Operators.ORD('C'), values)

    def testBasicSymbolic(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        #alloc/map a little mem
        size = 0x10000
        addr = mem.mmap(None, size, 'rwx')
        #initialize first 10 bytes as [100, 101, 102, .. 109]
        for i in xrange(10):
            mem[addr+i] = Operators.CHR(100+i)

        #initialize first 10 bytes as [100, 101, 102, .. 109]
        for i in xrange(10):
            self.assertEqual(mem[addr+i], Operators.CHR(100+i))


        #make a free symbol of 32 bits
        x = cs.new_bitvec(32) 
        #constraint it to range into [addr, addr+10)
        cs.add(x>=addr)
        cs.add(x<addr+10)

        #Well.. x is symbolic
        self.assertTrue(issymbolic(x))
        #It shall be a solution
        self.assertTrue(solver.check(cs))
        #if we ask for a possible solution (an x that comply with the constraints)
        sol = solver.get_value(cs, x)
        #it should comply..
        self.assertTrue(sol >= addr and sol<addr+10)

        #min and max value should be addr and addr+9
        m, M = solver.minmax(cs, x)
        self.assertEqual(m, addr)
        self.assertEqual(M, addr+9)

        #If we ask for all possible solutions...
        for val in solver.get_all_values(cs, x):
            #any solution must comply..
            self.assertTrue(sol >= addr and sol<addr+10)

        #so now lets ask the memory for values pointed by addr
        c = mem[x]
        for val in solver.get_all_values(cs, c):
            self.assertTrue(val>=100 and val<110)

        #constraint the address a litle more
        cs.add(x<=addr)
        #It shall be a solution
        self.assertTrue(solver.check(cs))
        #if we ask for a possible solution 
        sol = solver.get_value(cs, x)
        #it must be addr
        self.assertTrue(sol == addr)

        #lets ask the memory for the value under that address
        c = mem[x]
        sol = solver.get_value(cs, c)
        self.assertTrue(Operators.ORD(sol)==100)

        self.assertItemsEqual(mem[x:x+4], "defg")
        self.assertItemsEqual(mem[addr:addr+4], "defg")
        mem, x = pickle.loads(pickle.dumps((mem,x)))
        self.assertItemsEqual(mem[x:x+4], "defg")
        self.assertItemsEqual(mem[addr:addr+4], "defg")


    def testMultiSymbolic(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        #alloc/map a little mem
        size = 0x10000
        addr = mem.mmap(None, size, 'rwx')
        #initialize first 10 bytes as [100, 101, 102, .. 109]
        for i in xrange(addr, addr+10):
            mem[i] = Operators.CHR(100+i-addr)

        #Make a char that ranges from 'A' to 'Z'
        v = cs.new_bitvec(32) 
        cs.add(v>=Operators.ORD('A'))
        cs.add(v<=Operators.ORD('Z'))

        #assign it to the first 10 bytes
        mem[addr+5] = Operators.CHR(v)


        #mak a free symbol of 32 bits
        x = cs.new_bitvec(32) 
        #constraint it to range into [addr, addr+10)
        cs.add(x>=addr)
        cs.add(x<addr+10)

        #so now lets ask the memory for values pointed by addr
        c = mem[x]
        for val in solver.get_all_values(cs, c,1000):
            self.assertTrue(val>=100 and val<110 or val >= Operators.ORD('A') and val <= Operators.ORD('Z'))

    def testmprotectFailReading(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')
        mem[addr] = 'a'

        self.assertEqual(mem[addr], 'a')

        mem.mprotect(addr, size, 'w')
        self.assertRaisesRegexp(MemoryException, "No access reading <%08x>"%addr, mem.__getitem__, addr)


    def testmprotectFailSymbReading(self):
        cs = ConstraintSet()

        #In the beggining the solver was 'sat' ...
        self.assertTrue(solver.check(cs))


        mem = SMemory32(cs)

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x3000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'rwx')

        #okay we should have 1 map 
        self.assertEqual(len(mem.mappings()), 1)

        #free middle page
        mem.munmap(addr+0x1000 , 1)

        #And now just 2
        self.assertEqual(len(mem.mappings()), 2)

        #lets write some chars at the beginning of each page
        mem[addr] = 'a'
        mem[addr+0x2000] = 'b'

        #check it....
        self.assertEqual(mem[addr], 'a')
        self.assertEqual(mem[addr+0x2000], 'b')

        #make a free symbol of 32 bits
        x = cs.new_bitvec(32) 
        #constraint it to range into [addr, addr+10)
        cs.add(x>=addr)
        cs.add(x<=addr+0x2000)

        #Well.. x is symbolic
        self.assertTrue(issymbolic(x))
        #It shall be a solution
        self.assertTrue(solver.check(cs))
        #if we ask for a possible solution (an x that comply with the constraints)
        sol = solver.get_value(cs, x)
        #it should comply..
        self.assertTrue(sol >= addr and sol<=addr+0x2000)
        #print map(hex,sorted(solver.get_all_values(cs, x, 0x100000))),  map(hex,solver.minmax(cs, x)), mem[x]

                                                   #No Access Reading <4160741376>
        self.assertRaisesRegexp(MemoryException, r"No access reading.*", mem.__getitem__, x)

    def testmprotectFailWriting(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'wx')
        mem[addr] = 'a'
        mem.mprotect(addr, size, 'r')
        self.assertRaisesRegexp(MemoryException, "No access writing <%08x>"%addr, mem.__setitem__, addr, 'a')

    def testmprotecNoReadthenOkRead(self):
        mem = Memory32()

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)

        size = 0x10000
        #alloc/map a little mem
        addr = mem.mmap(None, size, 'wx')
        mem[addr] = 'a'

        self.assertRaisesRegexp(MemoryException, "No access reading <%08x>"%addr, mem.__getitem__, addr)

        mem.mprotect(addr, size, 'r')
        self.assertEqual(mem[addr], 'a')

    def test_COW(self):
        m = AnonMap(0x10000000, 0x2000, 'rwx')

        #Check the size
        self.assertEqual(len(m), 0x2000)

        #Set Some chars
        m[0x10001000:0x10001002] = 'AB'
        m[0x10002000-1] = 'Z'

        #check it is initialized with zero
        self.assertItemsEqual(m[0x10001000:0x10001002], 'AB')
        self.assertEqual(m[0x10002000-1], 'Z')
        self.assertItemsEqual(m[0x10001000:0x10002000], 'AB'+ 0xffd*'\x00' +'Z')

        #Make COW
        cow = COWMap(m, 0x1000)

        #Check COW length
        self.assertEqual(len(cow), 0x1000)

        #check it is initialized with zero
        self.assertItemsEqual(m[0x10001000:0x10001002], 'AB')
        self.assertEqual(m[0x10002000-1], 'Z')
        self.assertItemsEqual(m[0x10001000:0x10002000], 'AB'+ 0xffd*'\x00' +'Z')
        self.assertItemsEqual(cow[0x10001000:0x10002000], 'AB'+ 0xffd*'\x00' +'Z')

        #Set and check some chars
        cow[0x10001000:0x10001002] = 'ab'
        cow[0x10002000-1] = 'z'
        self.assertItemsEqual(cow[0x10001000:0x10001002], 'ab')
        self.assertEqual(cow[0x10002000-1], 'z')
        self.assertItemsEqual(m[0x10001000:0x10001002], 'AB')
        self.assertEqual(m[0x10002000-1], 'Z')
        self.assertItemsEqual(cow[0x10001000:0x10002000], 'ab'+ 0xffd*'\x00' +'z')


        #Set and check some chars
        cow[0x10002000-1] = 'z'
        self.assertEqual(cow[0x10001000], 'a')
        self.assertEqual(cow[0x10002000-1], 'z')
        self.assertEqual(m[0x10001000], 'A')
        self.assertEqual(m[0x10002000-1], 'Z')

    def test_pickle_mmap_anon(self):
        m = AnonMap(0x10000000, 0x3000, 'rwx')
        m[0x10001000] = 'A'
        s = StringIO(pickle.dumps(m))
        m = pickle.load(s)
        self.assertEqual(m[0x10001000], 'A')


    def test_pickle_mmap_file(self):
        #file mapping
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('X'*0x3000)
        rwx_file.close()
        m = FileMap(0x10000000, 0x3000, 'rwx', rwx_file.name)
        m[0x10000000] = 'Y'
        s = StringIO(pickle.dumps(m))
        m = pickle.load(s)
        self.assertEqual(m[0x10001000], 'X')
        self.assertEqual(m[0x10000000], 'Y')

    def test_pickle_mmap_anon_cow(self):
        m = AnonMap(0x10000000, 0x3000, 'rwx', 'X'*0x1000+'Y'*0x1000+'Z'*0x1000)
        m = COWMap(m)
        s = StringIO(pickle.dumps(m))
        m = pickle.load(s)
        self.assertEqual(m[0x10001000], 'Y')
        self.assertEqual(m.start, 0x10000000)
        self.assertEqual(m.end, 0x10003000)

    def test_pickle_mmap_anon_cow_offset(self):
        m = AnonMap(0x10000000, 0x3000, 'rwx', 'X'*0x1000+'Y'*0x1000+'Z'*0x1000)
        m = COWMap(m, offset=0x1000, size=0x1000)
        s = StringIO(pickle.dumps(m))
        m = pickle.load(s)
        self.assertEqual(m[0x10001000], 'Y')
        self.assertEqual(m.start, 0x10001000)
        self.assertEqual(m.end, 0x10002000)


    def test_pickle_mmap_file_cow(self):
        #file mapping
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('X'*0x1000+'Y'*0x1000+'Z'*0x1000)
        rwx_file.close()
        m = FileMap(0x10000000, 0x3000, 'rwx', rwx_file.name)
        m = COWMap(m)
        s = StringIO(pickle.dumps(m))
        m = pickle.load(s)
        self.assertEqual(m[0x10001000], 'Y')
        self.assertEqual(m.start, 0x10000000)
        self.assertEqual(m.end, 0x10003000)

    def test_pickle_mmap_file_cow_offset(self):
        #file mapping
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('X'*0x1000+'Y'*0x1000+'Z'*0x1000)
        rwx_file.close()
        m = FileMap(0x10000000, 0x3000, 'rwx', rwx_file.name)
        m = COWMap(m, size=0x1000, offset=0x1000)
        s = StringIO(pickle.dumps(m))
        m = pickle.load(s)
        self.assertEqual(m[0x10001000], 'Y')
        self.assertEqual(m.start, 0x10001000)
        self.assertEqual(m.end, 0x10002000)


    def test_pickle(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        #start with no maps
        self.assertEqual(len(mem.mappings()), 0)
        #alloc/map a byte
        addr_a = mem.mmap(None, 0x1000, 'r')

        #one map
        self.assertEqual(len(mem.mappings()), 1)

        #file mapping
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('a'*0x3000)
        rwx_file.close()
        addr_f = mem.mmapFile(0, 0x3000, 'rwx', rwx_file.name)
        mem.munmap(addr_f+0x1000, 0x1000)
        #two map2
        self.assertEqual(len(mem.mappings()), 3)

        sym = cs.new_bitvec(8)
        mem[addr_f] = sym

        #save it
        
        s = StringIO(pickle.dumps(mem))

        #load it
        mem1 = pickle.load(s)

        #two maps
        self.assertEqual(len(mem1.mappings()), 3)

        os.unlink(rwx_file.name)

    def testMultiSymbolicWrites(self):
        cs = ConstraintSet()
        mem = SMemory64(cs)
        mem.mmap(0x10000, 0x1000, 'rwx')
        self.assertEqual(len(mem.mappings()), 1)

        addr = cs.new_bitvec(64)
        cs.add(addr == 0x10000)
        value = cs.new_bitvec(8)
        cs.add(value == 0x41)
        mem[addr] = value

        self.assertEqual(solver.get_all_values(cs, mem[addr]), [0x41])

        addr1 = cs.new_bitvec(64)
        cs.add(Operators.OR(addr1 == 0x10000, addr1 == 0x10001))
        value1 = cs.new_bitvec(8)
        cs.add(value1 == 0x42)
        mem[addr1] = value1

        self.assertItemsEqual(solver.get_all_values(cs, mem[0x10000]), [0x41, 0x42])
        self.assertItemsEqual(solver.get_all_values(cs, mem[0x10001]), [0x00, 0x42])

        addr2 = cs.new_bitvec(64)
        cs.add(Operators.OR(addr2 == 0x10000, addr2 == 0x10001, addr2 == 0x10002))
        value2 = cs.new_bitvec(8)
        cs.add(value2 == 0x43)
        mem[addr2] = value2

        self.assertItemsEqual(solver.get_all_values(cs, mem[0x10000]), [0x41, 0x42, 0x43])
        self.assertItemsEqual(solver.get_all_values(cs, mem[0x10001]), [0x00,   0x42, 0x43])
        self.assertItemsEqual(solver.get_all_values(cs, mem[0x10002]), [0x00, 0x43])


    def test_mmap_file(self):
        #file mapping
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('X'*0x3000)
        rwx_file.close()
        m = FileMap(0x10000000, 0x3000, 'rwx', rwx_file.name)
        m[0x10000000:0x10000002] = 'YZ'
        self.assertEqual(m[0x10000000], 'Y')
        self.assertEqual(m[0x10000001], 'Z')
        self.assertItemsEqual(m[0x10000000:0x10000003], 'YZX')

        head, tail = m.split(0)
        self.assertEqual(head, None)
        self.assertEqual(tail, m)

        head, tail = m.split(0x10000000)
        self.assertEqual(head, None)
        self.assertEqual(tail, m)

        head, tail = m.split(0x10003001)
        self.assertEqual(head, head)
        self.assertEqual(tail, None)


        head, tail = m.split(0x10003000-1)
        self.assertEqual(len(head), 0x3000-1)
        self.assertEqual(len(tail), 1)

    def test_mmap_anon_split(self):
        #file mapping
        m = AnonMap(0x10000000, 0x3000, 'rwx')
        m[0x10000000:0x10000002] = 'YZ'
        self.assertEqual(m[0x10000000], 'Y')
        self.assertEqual(m[0x10000001], 'Z')
        self.assertItemsEqual(m[0x10000000:0x10000003], 'YZ\x00')

        head, tail = m.split(0)
        self.assertEqual(head, None)
        self.assertEqual(tail, m)

        head, tail = m.split(0x10000000)
        self.assertEqual(head, None)
        self.assertEqual(tail, m)

        head, tail = m.split(0x10003001)
        self.assertEqual(head, head)
        self.assertEqual(tail, None)


        head, tail = m.split(0x10003000-1)
        self.assertEqual(len(head), 0x3000-1)
        self.assertEqual(len(tail), 1)

        m = pickle.loads(pickle.dumps(m))
        self.assertItemsEqual(m[0x10000000:0x10000003], 'YZ\x00')


    def test_mmap_file_extra(self):
        #file mapping
        rwx_file = tempfile.NamedTemporaryFile('w+b', delete=False)
        rwx_file.file.write('X'*0x2800)
        rwx_file.close()
        m = FileMap(0x10000000, 0x3000, 'rwx', rwx_file.name)
        self.assertItemsEqual(m[0x10000000:0x10003000], 'X'*0x2800 + '\x00'*0x800)

        m[0x100027f0:0x10002810] = 'Y'*0x20
        self.assertItemsEqual(m[0x10000000:0x10003000], 'X'*0x27f0 + 'Y'*0x20 + '\x00'*0x7f0)

        m = pickle.loads(pickle.dumps(m))
        self.assertItemsEqual(m[0x10000000:0x10003000], 'X'*0x27f0 + 'Y'*0x20 + '\x00'*0x7f0)

    def test_mem_basic_trace(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        addr = mem.mmap(None, 0x1000, 'rw')

        mem.push_record_writes()
        mem.write(addr, 'a')
        mem.write(addr+1, 'b')
        writes = mem.pop_record_writes()

        self.assertIn((addr, ['a']), writes)
        self.assertIn((addr+1, ['b']), writes)


    def test_mem_trace_no_overwrites(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        addr = mem.mmap(None, 0x1000, 'rw')

        mem.push_record_writes()
        mem.write(addr, 'a')
        mem.write(addr, 'b')
        writes = mem.pop_record_writes()

        self.assertIn((addr, ['a']), writes)
        self.assertIn((addr, ['b']), writes)

    def test_mem_trace_nested(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)

        addr = mem.mmap(None, 0x1000, 'rw')

        mem.push_record_writes()
        mem.write(addr, 'a')
        mem.write(addr+1, 'b')
        mem.push_record_writes()
        mem.write(addr+2, 'c')
        mem.write(addr+3, 'd')
        inner_writes = mem.pop_record_writes()
        outer_writes = mem.pop_record_writes()

        # Make sure writes do not appear in a trace started after them
        self.assertNotIn((addr, ['a']), inner_writes)
        self.assertNotIn((addr+1, ['b']), inner_writes)
        # Make sure the first two are in the outer write
        self.assertIn((addr, ['a']), outer_writes)
        self.assertIn((addr+1, ['b']), outer_writes)
        # Make sure the last two are in the inner write
        self.assertIn((addr+2, ['c']), inner_writes)
        self.assertIn((addr+3, ['d']), inner_writes)
        # Make sure the last two are also in the outer write
        self.assertIn((addr+2, ['c']), outer_writes)
        self.assertIn((addr+3, ['d']), outer_writes)


    def test_mem_trace_ignores_failing(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        addr = mem.mmap(None, 0x1000, 'rw')

        mem.push_record_writes()
        with self.assertRaises(MemoryException):
            mem.write(addr-0x5000, 'a')
        trace = mem.pop_record_writes()

        # Make sure erroring writes don't get recorded
        self.assertEqual(len(trace), 0)


if __name__ == '__main__':
    unittest.main()

