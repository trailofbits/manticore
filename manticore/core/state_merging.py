from manticore.core.smtlib import solver, ConstraintSet


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
    return exp1 | exp2


def map_start(m):
    return m.start


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


def is_merge_possible(state1, state2):
    platform1 = state1.platform
    platform2 = state2.platform

    merged_exp = merge_constraints(state1.constraints, state2.constraints)
    merged_constraint = ConstraintSet()
    merged_constraint.add(merged_exp)

    # compare input and output sockets of the states
    if not compare_sockets(merged_constraint, platform1.input, platform2.input) or \
            not compare_sockets(merged_constraint, platform1.output, platform2.output):
        return False

    # compare symbolic files opened by the two states
    if platform1.symbolic_files != platform2.symbolic_files:
        return False

    # compare system call traces of the two states
    if len(platform1.syscall_trace) != len(platform2.syscall_trace):
        return False
    for i, (name1, fd1, data1) in enumerate(platform1.syscall_trace):
        (name2, fd2, data2) = platform2.syscall_trace[i]
        if not (name1 == name2 and fd1 == fd2 and compare_buffers(merged_constraint, data1, data2)):
            return False
    # compare memory of the two states
    if not compare_mem(state1.mem, state2.mem, merged_constraint):
        return False
    return True


#TODO
def merge(state1, state2):
    return state1


