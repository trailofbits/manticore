import itertools, struct

class BinaryObject(object):
    _fields_ = []

    def __init__(self):
        self._total_size = 0

    def __len__(self):
        return self._total_size

    def __repr__(self):
        result = ['{']
        for slot, fmt in self._fields_:
            if slot is None:
                continue
            if '[' in slot:
                slot = slot.split('[')[0]
            result.append(repr(slot)+':')
            result.append(repr(getattr(self,slot)))
        result.append('}')
        return ' '.join(result)
        
        
    def _initialize_slots(self, buf, offset, field_specs):
        total = self._total_size
        for slot, fmt in field_specs:
            reps = 1
            try:
                if '[' in slot:
                    reps = slot.split('[')[1][:-1]
                    slot = slot.split('[')[0]
                    try:
                        reps = int(reps)
                    except Exception,e:
                        reps = getattr(self, reps)
            except Exception,e:
                pass

            x = []
            size = 0
            for i in range(reps):
                if isinstance(fmt, type):
                    val = fmt.from_buf(buf, offset + total + size)
                    assert isinstance(val, BinaryObject)
                    x.append(val)
                    size += len(val)
                else:
                    try:
                        x += struct.unpack_from(fmt, buf, offset + total+ size)
                    except:
                        raise Exception("Failed parsing %s from offset %d"%(fmt,offset + total))
                    size += struct.calcsize(fmt)

                #print "PARSING %s of type %s REP %d at offset %d of size %d"%(slot, fmt, i, offset + total, size)
            total += size

            if reps == 1 and len(x) ==1:
                x = x[0]
            if slot is not None:
                setattr(self, slot, x)

        self._total_size = total

    @classmethod
    def from_buf(cls, buf, offset=0):
        # Determine our inheritance path back to BinaryObject
        inheritance_chain = []
        pos = cls
        while pos != BinaryObject:
            inheritance_chain.append(pos)
            bases = pos.__bases__
            assert len(bases) == 1
            pos = bases[0]
        inheritance_chain.reverse()

        # Determine all the field names and specs that we need to read.
        all_field_specs = itertools.chain(*[c._fields_
                                            for c in inheritance_chain])

        # Create the actual object and populate its fields.
        obj = cls()
        obj._initialize_slots(buf, offset, all_field_specs)
        return obj


class UserRegsStruct(BinaryObject):
    _fields_ = [('r15', '<Q'),
                ('r14', '<Q'),
                ('r13', '<Q'),
                ('r12', '<Q'),
                ('rbp', '<Q'),
                ('rbx', '<Q'),
                ('r11', '<Q'),
                ('r10', '<Q'),
                ('r9', '<Q'),
                ('r8', '<Q'),
                ('rax', '<Q'),
                ('rcx', '<Q'),
                ('rdx', '<Q'),
                ('rsi', '<Q'),
                ('rdi', '<Q'),
                ('orig_rax', '<Q'),
                ('rip', '<Q'),
                ('cs', '<Q'),
                ('eflags', '<Q'),
                ('rsp', '<Q'),
                ('ss', '<Q'),
                ('fs_base', '<Q'),
                ('gs_base', '<Q'),
                ('ds', '<Q'),
                ('es', '<Q'),
                ('fs', '<Q'),
                ('gs', '<Q')]

class FPUStackElement(BinaryObject):
    _fields_ = [
        ('mantissa', '<Q'),
        ('exponent', '<H'),
        (None, '6c')]

class FPUStack(BinaryObject):
    _fields_ = [
        ('st0', FPUStackElement),
        ('st1', FPUStackElement),
        ('st2', FPUStackElement),
        ('st3', FPUStackElement),
        ('st4', FPUStackElement),
        ('st5', FPUStackElement),
        ('st6', FPUStackElement),
        ('st7', FPUStackElement),]

class XMMReg(BinaryObject):
    _fields_ = [
        ('low', '<Q'),
        ('high', '<Q')]

class XMMSpace(BinaryObject):
    _fields_ = [
        ('xmm0', XMMReg),
        ('xmm1', XMMReg),
        ('xmm2', XMMReg),
        ('xmm3', XMMReg),
        ('xmm4', XMMReg),
        ('xmm5', XMMReg),
        ('xmm6', XMMReg),
        ('xmm7', XMMReg),
        ('xmm8', XMMReg),
        ('xmm9', XMMReg),
        ('xmm10', XMMReg),
        ('xmm11', XMMReg),
        ('xmm12', XMMReg),
        ('xmm13', XMMReg),
        ('xmm14', XMMReg),
        ('xmm15', XMMReg),]

class UserFpregsStruct(BinaryObject):
    _fields_ = [('cwd', '<H'),
                ('swd', '<H'),
                ('ftw', '<H'),
                ('fop', '<H'),
                ('rip', '<Q'),
                ('rdp', '<Q'),
                ('mxcsr', '<L'),
                ('mxcsr_mask', '<L'),
                ('st_space', FPUStack),
                ('xmm_space', XMMSpace),
                (None, '96c'),
          ]

class MappedRange32(BinaryObject):
    _fields_ = [('fd_offs', '<Q'),
                ('begin', '<L'),
                ('end', '<L'),
                ('is_r', 'B'),
                ('is_w', 'B'),
                ('is_x', 'B'),
                (None, '5c')]

class Grr(BinaryObject):
    _fields_ = [('magic', '4c'),
                ('exe_num','<L'),
                ('gregs', UserRegsStruct),
                ('fpregs', UserFpregsStruct),
                ('ranges[652]', MappedRange32) ] 

if __name__ == '__main__':
    import sys
    mbb = Grr.from_buf(file(sys.argv[1]).read())
    print mbb

