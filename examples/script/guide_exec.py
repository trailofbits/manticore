import sys
from manticore import Manticore

# This example demonstrates guiding Manticore's analysis
# by ignoring all branches to libc

def find_lib(m, name):
    for vmmap in m.memory:
        if vmmap.name == 'libc.so.6':
            return vmmap

if __name__ == '__main__':
    path = sys.argv[1]
    # Create a new Manticore object
    m = Manticore(path)

    # Now that binary is loaded, pull out where libc is mapped
    lib = find_lib(m, 'libc')
    if lib is None:
        sys.exit(1)

    # Ensure that we ignore all possible branches to libc
    # This hook returns False if we should abandon exploration
    # or True to continue
    def fork_hook(new_pc):
        _from, _to = lib.start, lib.start + lib.size
        return not (_from <= new_pc < _to)
    m.add_fork_hook(fork_hook)

    # Start path exploration. start() returns when Manticore
    # finishes
    m.start()
