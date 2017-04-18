
import sys
from manticore import Manticore

'''
Demonstrates the creation and copying of symbolic buffers.

Usage:

 $ gcc -static -g state_explore.c -o state_explore # -static is optional
 $ ADDRESS=0x$(objdump -S state_explore | grep -A 1 'value & 0xff' |
         tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
 $ python ./state_explore_sym.py state_explore $ADDRESS

'''

if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.stderr.write("Usage: %s [binary] [address]\n"%(sys.argv[0],))
        sys.exit(2)

    # Passing a parameter to state_explore binary disables reading the value
    # from STDIN, and relies on us adding it manually
    m = Manticore(sys.argv[1], ['anything'])

    # Uncomment to see debug output
    m.verbosity = 2

    # Set to the address of the conditonal checking for the first complex branch
    introduce_at = int(sys.argv[2], 0)

    @m.hook(introduce_at)
    def introduce_sym(state):
        print "Introducing symbolic value to {:x}".format(state.cpu.RBP-0xc)
        val = state.new_symbolic_buffer(4)
        state.cpu.write_bytes(state.cpu.RBP - 0xc, val)

    m.run()
