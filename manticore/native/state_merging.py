from ..core.smtlib import SelectedSolver, ConstraintSet, Operators, issymbolic, BitVec


def compare_sockets(cs, socket1, socket2):
    """
    This method compares Socket objects for equality using the buffer and peer attributes.
    It uses `compare_buffers` for checking buffer attributes for equality.
    It calls itself for comparing peer Socket objects.
    Returns True if the Socket objects are equal, false otherwise.
    :param cs: ConstraintSet to be used for checking Socket.buffer for semantic equality using `SelectedSolver.instance().must_be_true()`
    :param socket1: one of two Socket objects to be compared for equality against socket2
    :param socket2: one of two Socket objects to be compared for equality against socket1
    :return: True, if the Socket objects are found to be equal, False otherwise
    """
    if socket1 is None:
        return socket2 is None
    if socket2 is None:
        return socket1 is None
    if not compare_buffers(cs, socket1.buffer, socket2.buffer):
        return False
    return compare_sockets(cs, socket1.peer, socket2.peer)


def compare_buffers(cs, buffer1, buffer2):
    """
    This method compares the two List objects for equality using the `SelectedSolver.instance().must_be_true()` call.
    :param cs: ConstraintSet to be used for checking buffer1 for semantic equality with buffer2 using `SelectedSolver.instance().must_be_true()`
    :param buffer1: one of two List objects to be compared for equality against buffer2
    :param buffer2: one of two List objects to be compared for equality against buffer1
    :return: True, if the List objects are equal, False otherwise
    """
    if len(buffer1) != len(buffer2):
        return False
    for b1, b2 in zip(buffer1, buffer2):
        cond = cs.migrate(b1 == b2)
        if not SelectedSolver.instance().must_be_true(cs, cond):
            return False
    return True


def merge_constraints(constraints1, constraints2):
    """
    :param constraints1: one of two ConstraintSet objects to be merged
    :param constraints2: second of two ConstraintSet objects to be merged
    :return: (Expression, Expression, ConstraintSet) where the first and second Expression objects are conjunctions of
    of all the constraints in constraints1 and constraints2 respectively. The ConstraintSet is an object that contains
    a single constraint that is a logical OR of these two Expression objects.
    """
    exp1 = constraints1.constraints[0]
    for i in range(1, len(constraints1.constraints)):
        exp1 = exp1 & constraints1.constraints[i]
    exp2 = constraints2.constraints[0]
    for i in range(1, len(constraints2.constraints)):
        exp2 = exp2 & constraints2.constraints[i]
    merged_constraint = ConstraintSet()
    merged_constraint.add(exp1 | exp2)
    return exp1, exp2, merged_constraint


def compare_byte_vals(mem1, mem2, addr, merged_constraint):
    """
    Compares values in memory at address `addr`, returns True if they are semantically equal, False otherwise
    :param mem1: first of two memory objects we want to use for comparison
    :param mem2: second of two memory objects we want to use for comparison
    :param addr: address at which bytes values are to be compared
    :param merged_constraint: ConstraintSet to be used when using the call to `SelectedSolver.instance().must_be_true()`
    :return: returns True if 1 byte values at address `addr` in `mem1` and `mem2` are semantically equal, False otherwise
    """
    val1 = mem1.read(addr, 1)
    val2 = mem2.read(addr, 1)
    # since we only read a single byte value, these lists should only have one entry in them
    assert len(val1) == 1 and len(val2) == 1
    cond_to_check = merged_constraint.migrate(val1[0] == val2[0])
    if not SelectedSolver.instance().must_be_true(merged_constraint, cond_to_check):
        return False
    else:
        return True


# TODO move this comparison into an Executor API that uses an internal State API
def compare_mem(mem1, mem2, merged_constraint):
    """
    This method compares the number of maps, and then their names, permissions, start, and end values.
    If they all match, then it compares the concrete byte values for equality.
    If those match too, it then compares _symbols attribute values for equality if the two memory objects are of
    type SMemory.
    :param mem1: one of two memory objects to be compared
    :param mem2: second of two memory objects to be compared
    :param merged_constraint: ConstraintSet object that is to be used with `SelectedSolver.instance().must_be_true()` calls to check the
    memory objects for semantic equality
    :return: True, if the memory objects are equal, False otherwise
    """
    maps1 = sorted(list(mem1.maps))
    maps2 = sorted(list(mem2.maps))
    if len(maps1) != len(maps2):
        return False
    ret_val = None
    for m1, m2 in zip(maps1, maps2):
        if m1 != m2:  # compares the maps' names, permissions, starts, and ends
            ret_val = False
            break
        # Compare concrete byte values in the data in these memory maps for equality
        bytes1 = m1[m1.start : m1.end]
        bytes2 = m2[m2.start : m2.end]
        if bytes1 != bytes2:
            ret_val = False
            break
    checked_addrs = []
    # compare symbolic byte values in memory
    # hack to avoid importing SMemory because that import introduces a circular dependency on ManticoreBase
    if mem1.__class__.__name__ == "SMemory" and ret_val is not None:
        for addr1, _ in mem1._symbols.items():
            checked_addrs.append(addr1)
            if not compare_byte_vals(mem1, mem2, addr1, merged_constraint):
                ret_val = False
                break
    # hack to avoid importing SMemory because that import introduces a circular dependency on ManticoreBase
    if mem2.__class__.__name__ == "SMemory" and ret_val is not None:
        for addr2, _ in mem2._symbols.items():
            if addr2 not in checked_addrs:
                if not compare_byte_vals(mem1, mem2, addr2, merged_constraint):
                    ret_val = False
                    break
    if ret_val is not None:
        return ret_val
    else:
        return True


def is_merge_possible(state1, state2, merged_constraint):
    """
    Checks if a merge is possible by checking Input, Output sockets, symbolic_files, syscall_trace, and memory
    for equality.
    :param state1: one of two possible states we want to check for mergeability
    :param state2: second of two possible states we want to check for mergeability
    :param merged_constraint: ConstraintSet of merged constraints for state1 and state2
    :return: True, if state1 and state2 can be merged, False if otherwise
    """
    platform1 = state1.platform
    platform2 = state2.platform

    ret_val = None

    # compare input and output sockets of the states
    if not compare_sockets(
        merged_constraint, platform1.input, platform2.input
    ) or not compare_sockets(merged_constraint, platform1.output, platform2.output):
        ret_val = False, "inequivalent socket operations"

    # compare symbolic files opened by the two states
    if ret_val is None and platform1.symbolic_files != platform2.symbolic_files:
        ret_val = False, "inequivalent symbolic files"

    # compare system call traces of the two states
    if ret_val is None and len(platform1.syscall_trace) != len(platform2.syscall_trace):
        ret_val = False, "inequivalent syscall trace lengths"
    if ret_val is None:
        for i, (name1, fd1, data1) in enumerate(platform1.syscall_trace):
            (name2, fd2, data2) = platform2.syscall_trace[i]
            if not (
                name1 == name2 and fd1 == fd2 and compare_buffers(merged_constraint, data1, data2)
            ):
                ret_val = False, "inequivalent syscall traces"
                break

    # compare memory of the two states
    if ret_val is None and not compare_mem(state1.mem, state2.mem, merged_constraint):
        ret_val = False, "inequivalent memory"
    if ret_val is not None:
        return ret_val
    else:
        return True, None


def merge_cpu(cpu1, cpu2, state, exp1, merged_constraint):
    """
    Merge CPU objects into the state.CPU
    :param cpu1: one of two CPU objects that we wish to merge
    :param cpu2: second of two CPU objects that we wish to merge
    :param state: the state whose CPU attribute we will be updating
    :param exp1: the expression that if satisfiable will cause the CPU registers to take corresponding values from
    `cpu1`, else they will take corresponding values from `cpu2`
    :param merged_constraint: ConstraintSet under which we would want inequality between CPU register values to be
    satisfiable as checked using `SelectedSolver.instance().must_be_true()`
    :return: List of registers that were merged
    """
    merged_regs = []
    for reg in cpu1.canonical_registers:
        val1 = cpu1.read_register(reg)
        val2 = cpu2.read_register(reg)
        if isinstance(val1, BitVec) and isinstance(val2, BitVec):
            assert val1.size == val2.size
        if issymbolic(val1) or issymbolic(val2) or val1 != val2:
            val1_migrated = merged_constraint.migrate(val1)
            val2_migrated = merged_constraint.migrate(val2)
            if SelectedSolver.instance().must_be_true(
                merged_constraint, val1_migrated != val2_migrated
            ):
                merged_regs.append(reg)
                if cpu1.regfile.sizeof(reg) == 1:
                    state.cpu.write_register(reg, Operators.ITE(exp1, val1_migrated, val2_migrated))
                else:
                    state.cpu.write_register(
                        reg,
                        Operators.ITEBV(
                            cpu1.regfile.sizeof(reg), exp1, val1_migrated, val2_migrated
                        ),
                    )
    return merged_regs


def merge(state1, state2, exp1, merged_constraint):
    """
    Merge state1 and state2 into a single state
    :param state1:
    :param state2:
    :param exp1:
    :param merged_constraint:
    :return: the state that is the result of the merging of `state1` and `state2`
    """
    merged_state = state1
    merged_reg_list = merge_cpu(state1.cpu, state2.cpu, merged_state, exp1, merged_constraint)
    print("Merged registers: ")
    print(*merged_reg_list, sep=",")
    merged_state.constraints = merged_constraint
    return merged_state
