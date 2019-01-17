from manticore.core.smtlib import solver, ConstraintSet, Operators, issymbolic, BitVec


def compare_sockets(cs, socket1, socket2):
    if socket1 is None:
        return socket2 is None
    if socket2 is None:
        return socket1 is None
    if not compare_buffers(cs, socket1.buffer, socket2.buffer):
        return False
    return compare_sockets(cs, socket1.peer, socket2.peer)


def compare_buffers(cs, buffer1, buffer2):
    if len(buffer1) != len(buffer2):
        return False
    for b1, b2 in zip(buffer1, buffer2):
        if not solver.must_be_true(cs, b1 == b2):
            return False
    return True


def merge_constraints(constraints1, constraints2):
    exp1 = constraints1.constraints[0]
    for i in range(1, len(constraints1.constraints)):
        exp1 = exp1 & constraints1.constraints[i]
    exp2 = constraints2.constraints[0]
    for i in range(1, len(constraints2.constraints)):
        exp2 = exp2 & constraints2.constraints[i]
    merged_constraint = ConstraintSet()
    merged_constraint.add(exp1 | exp2)
    return exp1, exp2, merged_constraint


def compare_mem(mem1, mem2, merged_constraint):
    maps1 = sorted(list(mem1.maps))
    maps2 = sorted(list(mem2.maps))
    if len(maps1) != len(maps2):
        return False
    for m1, m2 in zip(maps1, maps2):
        if m1 != m2:  # compares the maps' names, permissions, starts, and ends
            return False
        # Compare concrete byte values in the data in these memory maps for equality
        bytes1 = m1[m1.start:m1.end]
        bytes2 = m2[m2.start:m2.end]
        if bytes1 != bytes2:
            return False
    # compare symbolic byte values in memory
    for addr1, _ in mem1._symbols.items():
        val1 = mem1.read(addr1, 1)
        val2 = mem2.read(addr1, 1)
        # since we only read a single byte value, these lists should only have one entry in them
        assert len(val1) == 1 and len(val2) == 1
        cond_to_check = (val1[0] == val2[0])
        if not solver.must_be_true(merged_constraint, cond_to_check):
            return False
    return True


def is_merge_possible(state1, state2, merged_constraint):
    platform1 = state1.platform
    platform2 = state2.platform

    # compare input and output sockets of the states
    if not compare_sockets(merged_constraint, platform1.input, platform2.input) or \
            not compare_sockets(merged_constraint, platform1.output, platform2.output):
        return False, "inequivalent socket operations"

    # compare symbolic files opened by the two states
    if platform1.symbolic_files != platform2.symbolic_files:
        return False, "inequivalent symbolic files"

    # compare system call traces of the two states
    if len(platform1.syscall_trace) != len(platform2.syscall_trace):
        return False, "inequivalent syscall trace lengths"
    for i, (name1, fd1, data1) in enumerate(platform1.syscall_trace):
        (name2, fd2, data2) = platform2.syscall_trace[i]
        if not (name1 == name2 and fd1 == fd2 and compare_buffers(merged_constraint, data1, data2)):
            return False, "inequivalent syscall traces"

    # compare memory of the two states
    if not compare_mem(state1.mem, state2.mem, merged_constraint):
        return False, "inequivalent memory"
    return True, None


#TODO
def merge_cpu(cpu1, cpu2, state, exp1, exp2):
    for reg in cpu1.canonical_registers:
        val1 = cpu1.read_register(reg)
        val2 = cpu2.read_register(reg)
        if isinstance(val1, BitVec) and isinstance(val2, BitVec):
            assert val1.size == val2.size
        if issymbolic(val1) or issymbolic(val2) or val1 != val2:
            if cpu1.regfile.sizeof(reg) == 1:
                state.cpu.write_register(reg, Operators.ITE(exp1, val1, val2))
            else:
                state.cpu.write_register(reg, Operators.ITEBV(cpu1.regfile.sizeof(reg), exp1, val1, val2))


def merge(state1, state2, exp1, exp2):
    merged_state = state1
    merge_cpu(state1.cpu, state2.cpu, merged_state, exp1, exp2)
    return merged_state


