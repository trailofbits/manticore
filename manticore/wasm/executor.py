# from ..utils.event import Eventful
from wasm.immtypes import (
    LocalVarXsImm,
    GlobalVarXsImm,
    MemoryImm,
    CurGrowMemImm,
    I32ConstImm,
    I64ConstImm,
    F32ConstImm,
    F64ConstImm,
)
from .types import I32, I64, F32, F64, Value
from ..core.smtlib import Operators, BitVec, issymbolic
from ..core.state import Concretize


class Trap(Exception):
    pass


class Executor(object):  # TODO - should be Eventful
    def __init__(self, *args, **kwargs):

        self._mapping = {
            0x00: self.unreachable,
            0x01: self.nop,
            0x02: self.nop,  # block
            0x03: self.nop,  # loop
            0x04: self.nop,  # if
            0x05: self.nop,  # else
            0x0B: self.nop,  # end
            0x0C: self.nop,  # br
            0x0D: self.nop,  # br_if
            0x0E: self.nop,  # br_table
            0x0F: self.nop,  # return
            0x10: self.nop,  # call
            0x11: self.nop,  # call_indirect
            0x1A: self.drop,
            0x1B: self.select,
            0x20: self.get_local,
            0x21: self.set_local,
            0x22: self.tee_local,
            0x23: self.get_global,
            0x24: self.set_global,
            0x28: self.i32_load,
            0x29: self.i64_load,
            0x2A: self.f32_load,
            0x2B: self.f64_load,
            0x2C: self.i32_load8_s,
            0x2D: self.i32_load8_u,
            0x2E: self.i32_load16_s,
            0x2F: self.i32_load16_u,
            0x30: self.i64_load8_s,
            0x31: self.i64_load8_u,
            0x32: self.i64_load16_s,
            0x33: self.i64_load16_u,
            0x34: self.i64_load32_s,
            0x35: self.i64_load32_u,
            0x36: self.i32_store,
            0x37: self.i64_store,
            0x38: self.f32_store,
            0x39: self.f64_store,
            0x3A: self.i32_store8,
            0x3B: self.i32_store16,
            0x3C: self.i64_store8,
            0x3D: self.i64_store16,
            0x3E: self.i64_store32,
            0x3F: self.current_memory,
            0x40: self.grow_memory,
            0x41: self.i32_const,
            0x42: self.i64_const,
            0x43: self.f32_const,
            0x44: self.f64_const,
            0x45: self.i32_eqz,
            0x46: self.i32_eq,
            0x47: self.i32_ne,
            0x48: self.i32_lt_s,
            0x49: self.i32_lt_u,
            0x4A: self.i32_gt_s,
            0x4B: self.i32_gt_u,
            0x4C: self.i32_le_s,
            0x4D: self.i32_le_u,
            0x4E: self.i32_ge_s,
            0x4F: self.i32_ge_u,
            0x50: self.i64_eqz,
            0x51: self.i64_eq,
            0x52: self.i64_ne,
            0x53: self.i64_lt_s,
            0x54: self.i64_lt_u,
            0x55: self.i64_gt_s,
            0x56: self.i64_gt_u,
            0x57: self.i64_le_s,
            0x58: self.i64_le_u,
            0x59: self.i64_ge_s,
            0x5A: self.i64_ge_u,
            0x5B: self.f32_eq,
            0x5C: self.f32_ne,
            0x5D: self.f32_lt,
            0x5E: self.f32_gt,
            0x5F: self.f32_le,
            0x60: self.f32_ge,
            0x61: self.f64_eq,
            0x62: self.f64_ne,
            0x63: self.f64_lt,
            0x64: self.f64_gt,
            0x65: self.f64_le,
            0x66: self.f64_ge,
            0x67: self.i32_clz,
            0x68: self.i32_ctz,
            0x69: self.i32_popcnt,
            0x6A: self.i32_add,
            0x6B: self.i32_sub,
            0x6C: self.i32_mul,
            0x6D: self.i32_div_s,
            0x6E: self.i32_div_u,
            0x6F: self.i32_rem_s,
            0x70: self.i32_rem_u,
            0x71: self.i32_and,
            0x72: self.i32_or,
            0x73: self.i32_xor,
            0x74: self.i32_shl,
            0x75: self.i32_shr_s,
            0x76: self.i32_shr_u,
            0x77: self.i32_rotl,
            0x78: self.i32_rotr,
            0x79: self.i64_clz,
            0x7A: self.i64_ctz,
            0x7B: self.i64_popcnt,
            0x7C: self.i64_add,
            0x7D: self.i64_sub,
            0x7E: self.i64_mul,
            0x7F: self.i64_div_s,
            0x80: self.i64_div_u,
            0x81: self.i64_rem_s,
            0x82: self.i64_rem_u,
            0x83: self.i64_and,
            0x84: self.i64_or,
            0x85: self.i64_xor,
            0x86: self.i64_shl,
            0x87: self.i64_shr_s,
            0x88: self.i64_shr_u,
            0x89: self.i64_rotl,
            0x8A: self.i64_rotr,
            0x8B: self.f32_abs,
            0x8C: self.f32_neg,
            0x8D: self.f32_ceil,
            0x8E: self.f32_floor,
            0x8F: self.f32_trunc,
            0x90: self.f32_nearest,
            0x91: self.f32_sqrt,
            0x92: self.f32_add,
            0x93: self.f32_sub,
            0x94: self.f32_mul,
            0x95: self.f32_div,
            0x96: self.f32_min,
            0x97: self.f32_max,
            0x98: self.f32_copysign,
            0x99: self.f64_abs,
            0x9A: self.f64_neg,
            0x9B: self.f64_ceil,
            0x9C: self.f64_floor,
            0x9D: self.f64_trunc,
            0x9E: self.f64_nearest,
            0x9F: self.f64_sqrt,
            0xA0: self.f64_add,
            0xA1: self.f64_sub,
            0xA2: self.f64_mul,
            0xA3: self.f64_div,
            0xA4: self.f64_min,
            0xA5: self.f64_max,
            0xA6: self.f64_copysign,
            0xA7: self.i32_wrap_i64,
            0xA8: self.i32_trunc_s_f32,
            0xA9: self.i32_trunc_u_f32,
            0xAA: self.i32_trunc_s_f64,
            0xAB: self.i32_trunc_u_f64,
            0xAC: self.i64_extend_s_i32,
            0xAD: self.i64_extend_u_i32,
            0xAE: self.i64_trunc_s_f32,
            0xAF: self.i64_trunc_u_f32,
            0xB0: self.i64_trunc_s_f64,
            0xB1: self.i64_trunc_u_f64,
            0xB2: self.f32_convert_s_i32,
            0xB3: self.f32_convert_u_i32,
            0xB4: self.f32_convert_s_i64,
            0xB5: self.f32_convert_u_i64,
            0xB6: self.f32_demote_f64,
            0xB7: self.f64_convert_s_i32,
            0xB8: self.f64_convert_u_i32,
            0xB9: self.f64_convert_s_i64,
            0xBA: self.f64_convert_u_i64,
            0xBB: self.f64_promote_f32,
            0xBC: self.i32_reinterpret_f32,
            0xBD: self.i64_reinterpret_f64,
            0xBE: self.f32_reinterpret_i32,
            0xBF: self.f64_reinterpret_i64,
        }

    def dispatch(self, inst: "Instruction", store: "Store", stack: "Stack"):
        opcode = inst.opcode
        assert opcode in self._mapping
        func = self._mapping[opcode]
        if inst.imm:
            return func(store, stack, inst.imm)
        else:
            return func(store, stack)

    def unreachable(self, store: "Store", stack: "Stack"):
        raise Trap()

    def nop(self, store: "Store", stack: "Stack"):
        pass

    def drop(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(Value.__args__, 1)
        stack.pop()

    def select(self, store: "Store", stack: "Stack"):
        c = stack.pop()
        v2 = stack.pop()
        v1 = stack.pop()
        assert isinstance(c, (I32, BitVec)), f"{type(c)} is not I32"
        if not issymbolic(v2) and not issymbolic(v1):
            assert type(v2) == type(v1), f"{type(v2)} is not the same as {type(v1)}"

        if issymbolic(c):

            # def setstate(state, value):
            #     state.platform.stack.data[-1] = I32(value)
            #
            # raise Concretize("Concretizing stack variable c", c, setstate=setstate)
            stack.push(Operators.ITEBV(32, c != 0, v1, v2))
        else:
            if c != 0:
                stack.push(v1)
            else:
                stack.push(v2)

    def get_local(self, store: "Store", stack: "Stack", imm: LocalVarXsImm):
        f = stack.get_frame().frame
        assert imm.local_index in range(len(f.locals))
        stack.push(f.locals[imm.local_index])

    def set_local(self, store: "Store", stack: "Stack", imm: LocalVarXsImm):
        f = stack.get_frame().frame
        assert imm.local_index in range(len(f.locals))
        stack.has_type_on_top(Value.__args__, 1)
        f.locals[imm.local_index] = stack.pop()

    def tee_local(self, store: "Store", stack: "Stack", imm: LocalVarXsImm):
        stack.has_type_on_top(Value.__args__, 1)
        v = stack.pop()
        stack.push(v)
        stack.push(v)
        self.set_local(store, stack, imm)

    def get_global(self, store: "Store", stack: "Stack", imm: GlobalVarXsImm):
        f = stack.get_frame().frame
        assert imm.global_index in range(len(f.module.globaladdrs))
        a = f.module.globaladdrs[imm.global_index]
        assert a in range(len(store.globals))
        glob = store.globals[a]
        stack.push(glob.value)

    def set_global(self, store: "Store", stack: "Stack", imm: GlobalVarXsImm):
        f = stack.get_frame().frame
        assert imm.global_index in range(len(f.module.globaladdrs))
        a = f.module.globaladdrs[imm.global_index]
        assert a in range(len(store.globals))
        stack.has_type_on_top(Value.__args__, 1)
        store.globals[a].value = stack.pop()

    def i32_load(self, store: "Store", stack: "Stack", imm: MemoryImm):
        f = stack.get_frame().frame
        assert f.module.memaddrs
        a = f.module.memaddrs[0]
        assert a in range(len(store.mems))
        mem = store.mems[a]
        assert isinstance(stack.peek(), I32), f"{type(stack.peek())} is not I32"
        i = stack.pop()
        ea = i + imm.offset
        if (ea + 4) > len(mem.data):
            raise Trap()
        c = Operators.CONCAT(32, *map(Operators.ORD, reversed(mem.data[ea : ea + 4])))
        stack.push(I32.cast(c))

    def i64_load(self, store: "Store", stack: "Stack", imm: MemoryImm):
        f = stack.get_frame().frame
        assert f.module.memaddrs
        a = f.module.memaddrs[0]
        assert a in range(len(store.mems))
        mem = store.mems[a]
        assert isinstance(stack.peek(), I32), f"{type(stack.peek())} is not I32"
        i = stack.pop()
        ea = i + imm.offset
        if (ea + 8) > len(mem.data):
            raise Trap()
        c = Operators.CONCAT(64, *map(Operators.ORD, reversed(mem.data[ea : ea + 8])))
        stack.push(I64.cast(c))

    def int_load(
        self, store: "Store", stack: "Stack", imm: MemoryImm, ty: type, size: int, signed: bool
    ):
        assert ty in {I32, I64}, f"{type(ty)} is not an I32 or I64"
        f = stack.get_frame().frame
        assert f.module.memaddrs
        a = f.module.memaddrs[0]
        assert a in range(len(store.mems))
        mem = store.mems[a]
        assert isinstance(stack.peek(), I32), f"{type(stack.peek())} is not I32"
        i = stack.pop()
        ea = i + imm.offset
        c = Operators.CONCAT(size, *map(Operators.ORD, reversed(mem.data[ea : ea + (size // 8)])))
        width = 32 if ty is I32 else 64
        if signed:
            c = Operators.SEXTEND(c, size, width)
        else:
            c = Operators.ZEXTEND(c, width)
        stack.push(ty.cast(c))

    def i32_load8_s(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I32, 8, True)

    def i32_load8_u(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I32, 8, False)

    def i32_load16_s(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I32, 16, True)

    def i32_load16_u(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I32, 16, False)

    def i64_load8_s(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I64, 8, True)

    def i64_load8_u(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I64, 8, False)

    def i64_load16_s(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I64, 16, True)

    def i64_load16_u(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I64, 16, False)

    def i64_load32_s(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I64, 32, True)

    def i64_load32_u(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_load(store, stack, imm, I32, 64, True)

    def int_store(self, store: "Store", stack: "Stack", imm: MemoryImm, ty: type, n=None):
        f = stack.get_frame().frame
        assert f.module.memaddrs
        a = f.module.memaddrs[0]
        assert a in range(len(store.mems))
        mem = store.mems[a]
        assert isinstance(stack.peek(), (ty, BitVec))
        c = stack.pop()
        assert isinstance(stack.peek(), I32)
        i = stack.pop()
        ea = i + imm.offset
        N = n if n else {I32: 32, I64: 64}[ty]
        if (ea + (N // 8)) > len(mem.data):
            raise Trap()
        if n:
            raise NotImplementedError("TODO")
        else:
            b = [Operators.CHR(Operators.EXTRACT(c, offset, 8)) for offset in range(0, N, 8)]

        for idx, v in enumerate(b):
            mem.data[ea + idx] = v

    def i32_store(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I32)

    def i64_store(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I64)

    def i32_store8(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I32, 8)

    def i32_store16(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I32, 16)

    def i64_store8(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I64, 8)

    def i64_store16(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I64, 16)

    def i64_store32(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.int_store(store, stack, imm, I64, 32)

    def current_memory(self, store: "Store", stack: "Stack", imm: CurGrowMemImm):
        f = stack.get_frame().frame
        assert f.module.memaddrs
        a = f.module.memaddrs[0]
        assert a in range(len(store.mems))
        mem = store.mems[a]
        stack.push(I32(len(mem.data) // 65536))

    def grow_memory(self, store: "Store", stack: "Stack", imm: CurGrowMemImm):
        raise NotImplementedError("grow_memory")

    def i32_const(self, store: "Store", stack: "Stack", imm: I32ConstImm):
        stack.push(I32.cast(imm.value))

    def i64_const(self, store: "Store", stack: "Stack", imm: I64ConstImm):
        stack.push(I64(imm.value))

    def i32_eqz(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 1)
        c1 = stack.pop()
        v = c1 == 0
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_eq(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c2 == c1
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_ne(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c2 != c1
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_lt_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 < c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_lt_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.ULT(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_gt_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 > c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_gt_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.UGT(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_le_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 <= c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_le_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.ULE(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_ge_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 >= c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_ge_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.UGE(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_eqz(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 1)
        c1 = stack.pop()
        v = c1 == 0
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_eq(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c2 == c1
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_ne(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c2 != c1
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_lt_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 < c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_lt_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.ULT(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_gt_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 > c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_gt_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.UGT(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_le_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 <= c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_le_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.ULE(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_ge_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = c1 >= c2
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i64_ge_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        v = Operators.UGE(c1, c2)
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, I32(1), I32(0)))
        else:
            stack.push(I32.cast(I32(1) if v else I32(0)))

    def i32_clz(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.clz")

    def i32_ctz(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.ctz")

    def i32_popcnt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.popcnt")

    def i32_add(self, store: "Store", stack: "Stack"):
        # The x86 module has a complicated way of doing addition. TODO - is that necessary for WASM?
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast((c2 + c1) % 2 ** 32))

    def i32_sub(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast((c1 - c2 + 2 ** 32) % 2 ** 32))

    def i32_mul(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast((c2 * c1) % 2 ** 32))

    def i32_div_s(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.div_s")

    def i32_div_u(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.div_u")

    def i32_rem_s(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.rem_s")

    def i32_rem_u(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.rem_u")

    def i32_and(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast(c2 & c1))

    def i32_or(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast(c2 | c1))

    def i32_xor(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast(c2 ^ c1))

    def i32_shl(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast(c2 << (c1 % 32)))

    def i32_shr_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast(Operators.SAR(32, c2, (c1 % 32))))

    def i32_shr_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I32, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I32.cast(c2 >> (c1 % 32)))

    def i32_rotl(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.rotl")

    def i32_rotr(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.rotr")

    def i64_clz(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.clz")

    def i64_ctz(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.ctz")

    def i64_popcnt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.popcnt")

    def i64_add(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast((c2 + c1) % 2 ** 64))

    def i64_sub(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast((c1 - c2 + 2 ** 64) % 2 ** 64))

    def i64_mul(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast((c2 * c1) % 2 ** 64))

    def i64_div_s(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.div_s")

    def i64_div_u(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.div_u")

    def i64_rem_s(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.rem_s")

    def i64_rem_u(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.rem_u")

    def i64_and(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast(c2 & c1))

    def i64_or(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast(c2 | c1))

    def i64_xor(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast(c2 ^ c1))

    def i64_shl(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast(c2 << (c1 % 64)))

    def i64_shr_s(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast(Operators.SAR(64, c2, c1 % 64)))

    def i64_shr_u(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(I64, 2)
        c2 = stack.pop()
        c1 = stack.pop()
        stack.push(I64.cast(c2 >> (c1 % 64)))

    def i64_rotl(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.rotl")

    def i64_rotr(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.rotr")

    def i32_wrap_i64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.wrap/i64")

    def i32_trunc_s_f32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.trunc_s/f32")

    def i32_trunc_u_f32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.trunc_u/f32")

    def i32_trunc_s_f64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.trunc_s/f64")

    def i32_trunc_u_f64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.trunc_u/f64")

    def i64_extend_s_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.extend_s/i32")

    def i64_extend_u_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.extend_u/i32")

    def i64_trunc_s_f32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.trunc_s/f32")

    def i64_trunc_u_f32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.trunc_u/f32")

    def i64_trunc_s_f64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.trunc_s/f64")

    def i64_trunc_u_f64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.trunc_u/f64")

    def i32_reinterpret_f32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i32.reinterpret/f32")

    def i64_reinterpret_f64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("i64.reinterpret/f64")



    def float_load( self, store: "Store", stack: "Stack", imm: MemoryImm, ty: type):
        if ty==F32:
            size=32
        elif ty==F64:
            size=64
        f = stack.get_frame()
        a = f.module.memaddrs[0]
        mem = store.mems[a]
        i = stack.pop()
        ea = i + imm.offset
        c = Operators.CONCAT(size, *map(Operators.ORD, reversed(mem.data[ea : ea + (size // 8)])))
        ret = ty.cast(c)
        stack.push(ret)

    # Floating point instructions
    def f32_load(self, store: "Store", stack: "Stack", imm: MemoryImm):
        return self.float_load(store, stack, imm, F32)

    def f64_load(self, store: "Store", stack: "Stack", imm: MemoryImm):
        return self.float_load(store, stack, imm, F64)

    def float_store(self, store: "Store", stack: "Stack", imm: MemoryImm, ty: type, n=None):
        f = stack.get_frame()
        a = f.module.memaddrs[0]
        mem = store.mems[a]
        c = stack.pop()
        i = stack.pop()
        ea = i + imm.offset
        if ty==F32:
            size=32
        else:
            size=64
        b = [Operators.CHR(Operators.EXTRACT(c, offset, 8)) for offset in range(0, size, 8)]
        for idx, v in enumerate(b):
            mem.data[ea + idx] = v

    def f32_pushValue(self, stack, v):
        if issymbolic(v):
            stack.push(Operators.ITEBV(32, v, F32(1), F32(0)))
        else:
            stack.push(F32.cast(F32(1) if v else F32(0)))

    def f32_store(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.float_store(store, stack, imm, F32)

    def f64_store(self, store: "Store", stack: "Stack", imm: MemoryImm):
        self.float_store(store, stack, imm, F64)

    def f32_const(self, store: "Store", stack: "Stack", imm: F32ConstImm):
        stack.push(F32(imm.value))

    def f64_const(self, store: "Store", stack: "Stack", imm: F64ConstImm):
        stack.push(F64(imm.value))

    def f32_eq(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(F32,2)
        v2 = stack.pop()
        v1 = stack.pop()
        v = (v1==v2)
        self.f32_pushValue(stack, v)

    def f32_ne(self, store: "Store", stack: "Stack"):
        stack.has_type_on_top(F32,2)
        v2 = stack.pop()
        v1 = stack.pop()
        v = (v1!=v2)
        self.f32_pushValue(stack,v)
        

    def f32_lt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.lt")

    def f32_gt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.gt")

    def f32_le(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.le")

    def f32_ge(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.ge")

    def f64_eq(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.eq")

    def f64_ne(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.ne")

    def f64_lt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.lt")

    def f64_gt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.gt")

    def f64_le(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.le")

    def f64_ge(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.ge")

    def f32_abs(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.abs")

    def f32_neg(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.neg")

    def f32_ceil(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.ceil")

    def f32_floor(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.floor")

    def f32_trunc(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.trunc")

    def f32_nearest(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.nearest")

    def f32_sqrt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.sqrt")

    def f32_add(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.add")

    def f32_sub(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.sub")

    def f32_mul(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.mul")

    def f32_div(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.div")

    def f32_min(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.min")

    def f32_max(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.max")

    def f32_copysign(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.copysign")

    def f64_abs(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.abs")

    def f64_neg(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.neg")

    def f64_ceil(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.ceil")

    def f64_floor(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.floor")

    def f64_trunc(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.trunc")

    def f64_nearest(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.nearest")

    def f64_sqrt(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.sqrt")

    def f64_add(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.add")

    def f64_sub(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.sub")

    def f64_mul(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.mul")

    def f64_div(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.div")

    def f64_min(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.min")

    def f64_max(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.max")

    def f64_copysign(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.copysign")

    def f32_convert_s_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.convert_s/i32")

    def f32_convert_u_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.convert_u/i32")

    def f32_convert_s_i64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.convert_s/i64")

    def f32_convert_u_i64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.convert_u/i64")

    def f32_demote_f64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.demote/f64")

    def f64_convert_s_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.convert_s/i32")

    def f64_convert_u_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.convert_u/i32")

    def f64_convert_s_i64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.convert_s/i64")

    def f64_convert_u_i64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.convert_u/i64")

    def f64_promote_f32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.promote/f32")

    def f32_reinterpret_i32(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f32.reinterpret/i32")

    def f64_reinterpret_i64(self, store: "Store", stack: "Stack"):
        raise NotImplementedError("f64.reinterpret/i64")
