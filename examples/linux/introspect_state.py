from manticore.native import Manticore
from manticore.core.plugin import StateDescriptor
from manticore.utils.enums import StateStatus
from time import sleep
import typing
import argparse

parser = argparse.ArgumentParser(
    description="Explore a binary with Manticore and print the tree of states"
)
parser.add_argument(
    "binary", type=str, nargs="?", default="binaries/multiple-styles", help="The program to run",
)
args = parser.parse_args()


def print_fork_tree(states: typing.Dict[int, StateDescriptor]):
    """
    Performs a depth-first traversal of the state tree, where each branch is a different fork
    """

    def df_print(state_id, depth=0):
        state = states[state_id]

        # Prepare a debug message about the state based on its current status
        msg = ""
        if state.status == StateStatus.running:
            msg = "(Exec {} ins)".format(state.own_execs if state.own_execs is not None else 0)
        elif state.status == StateStatus.waiting_for_solver:
            msg = "(Solving)"
        elif state.status == StateStatus.waiting_for_worker:
            msg = "(Waiting)"
        elif state.status == StateStatus.stopped:
            msg = "({})".format(state.termination_msg)

        # Print nice pretty arrows showing parenthood
        if depth == 0:
            print(state_id, msg)
        else:
            print("     " * (depth - 1) + "└-->", state_id, msg)

        # Prioritize states with fewer (or no) children since it gives us a nicer tree in the common case
        for c_st in sorted(state.children, key=lambda k: len(states[k].children)):
            df_print(c_st, depth + 1)

    # Only works if all states fork from the initial state
    df_print(0)
    print()


def run_every(callee: typing.Callable, duration: int = 3) -> typing.Callable:
    """
    Returns a function that calls <callee> every <duration> seconds
    """

    def inner(thread):  # Takes `thread` as argument, which is provided by the daemon thread API
        while True:
            # Pass Manticore's state descriptor dict to the callee
            callee(thread.manticore.introspect())
            sleep(duration)

    return inner


m = Manticore(args.binary)

# Tell Manticore to run `print_fork_tree` every second
m.register_daemon(run_every(print_fork_tree, 1))

m.run()

sleep(1)
print("Final fork tree:")
print_fork_tree(m.introspect())
