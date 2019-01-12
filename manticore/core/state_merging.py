from manticore.core.smtlib import solver, ConstraintSet


def compare_sockets(cs, socket1, socket2):
    if socket1 is None:
        return socket2 is None
    if socket2 is None:
        return socket1 is None
    for i in range(len(socket1.buffer)):
        if not solver.must_be_true(cs, socket1.buffer[i] == socket2.buffer[i]):
            return False
    return compare_sockets(cs, socket1.peer, socket2.peer)

#TODO
def merge_constraints(constraints1, constraints2):
    exp1 = constraints1.constraints[0]
    for i in range(1, len(constraints1.constraints)):
        exp1 = exp1 & constraints1.constraints[i]
    exp2 = constraints2.constraints[0]
    for i in range(1, len(constraints2.constraints)):
        exp2 = exp2 & constraints2.constraints[i]
    return exp1 | exp2


def is_merge_possible(state1, state2):
    # compare platform.files
    platform1 = state1.platform
    platform2 = state2.platform

    merged_exp = merge_constraints(state1.constraints, state2.constraints)
    merged_constraint = ConstraintSet()
    merged_constraint.add(merged_exp)

    # compare platform.input
    if not compare_sockets(merged_constraint, platform1.input, platform2.input) or \
            not compare_sockets(merged_constraint, platform1.output, platform2.output):
        return False

    # compare platform.symbolic_files
    # if platform1.symbolic_files != platform2.symbolic_files:
    #     return False

    # compare platform.syscall_trace
    # if platform1.syscall_trace != platform2.syscall_trace:
    #     return False

    # if platform1.mem != platform2.mem:
    #     return False

    return False
#TODO
def merge(state1, state2):
    return state1


