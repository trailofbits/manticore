from manticore.core.smtlib import Operators

class Memory:  #todo Mock
    def getchar(self, addr):
        raise NotImplementedError("getchar")
    def putchar(self, addr, value):
        raise NotImplementedError("putchar")

class Mem(object):
    ''' Mocking class for memory '''
    def __init__(self, mem):
        self.mem = dict(mem)
    def getchar(self, addr):
        #print "getchar",hex(addr), "%02x"%ord(self.mem[addr])
        return self.mem[addr]
    def putchar(self, addr, char):
        #print "putchar",hex(addr), "%02x"%ord(char)
        self.mem[addr]=char
    def read(self, addr, size):
        #print "read", hex(addr), size
        result = ''
        for i in xrange(size):
            result+=self.mem[addr+i]
        return result
    def write(self, addr, data):
        for i in xrange(len(data)):
            self.mem[addr+i]=data[i]
    def isExecutable(self, addr):
        return True
    def isWritable(self, addr):
        return True
    def isReadable(self, addr):
        return True

class SMem(object):
    ''' Mocking class for memory '''
    def __init__(self, array, init):
        self.code = {}
        self.mem = array
        for addr, val in init.items():
            self.mem[addr] = val

    def getchar(self, addr):
        if isinstance(addr, (int,long)) and addr in self.code.keys():
            return self.code[addr]
        return self.mem[addr]

    def putchar(self, addr, char):
        assert isinstance(addr,(int,long))
        assert isinstance(char,str) and len(char) == 1
        self.mem[addr]=char

    def read(self, addr, size):
        result = []
        for i in xrange(size):
            result.append(Operators.CHR(self.mem[addr+i]))
        return result

    def write(self, addr, data):
        for i in xrange(len(data)):
            self.mem[addr+i]=data[i]

    def isExecutable(self, addr):
        return True
    def isReadable(self, addr):
        return True
    def isWritable(self, addr):
        return True
