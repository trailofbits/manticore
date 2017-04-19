
import sys
from manticore import Manticore

'''
Replaces a variable that controls program flow with a symbolic buffer. This
in turn explores all possible states under that variable's influence.

Usage:

 $ gcc -static -g state_explore.c -o state_explore # -static is optional
 $ ADDRESS=0x$(objdump -S state_explore | grep -A 1 '((value & 0xff) != 0)' |
         tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
 $ python ./introduce_symbolic_bytes.py state_explore $ADDRESS

'''

if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.stderr.write("Usage: %s [binary] [address]\n"%(sys.argv[0],))
        sys.exit(2)

    # Passing a parameter to state_explore binary disables reading the value
    # from STDIN, and relies on us adding it manually
    m = Manticore(sys.argv[1], ['anything'])

    # Uncomment to see debug output
    #m.verbosity = 2

    # Set to the address of the instruction before the first conditional.
    introduce_at = int(sys.argv[2], 0)

    @m.hook(introduce_at)
    def introduce_sym(state):
        # RBP-0xC is the location of the value we're interested in:
        #
        #    if ((value & 0xff) != 0) {
        #  400a08:       8b 45 f4                mov    -0xc(%rbp),%eax
        #  400a0b:       0f b6 c0                movzbl %al,%eax
        #  400a0e:       85 c0                   test   %eax,%eax
        #

        print "introducing symbolic value to {:x}".format(state.cpu.RBP-0xc)

        val = state.new_symbolic_buffer(4)
        # Can also be achieved by:
        #val = state.symbolicate_buffer('++++')
        state.cpu.write_bytes(state.cpu.RBP - 0xc, val)

    m.run()
