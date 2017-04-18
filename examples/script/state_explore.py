
import sys
from manticore import Manticore

'''
Demonstrates guiding Manticore's state exploration. 

Usage:

 $ gcc -static -g state_explore.c -o state_explore # -static is optional
 $ ADDRESS=0x$(objdump -S state_explore | grep -A 1 'value == 0x41' |
         tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
 $ python ./state_explore.py state_explore $ADDRESS

'''

if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.stderr.write("Usage: %s [binary] [address]\n"%(sys.argv[0],))
        sys.exit(2)

    m = Manticore(sys.argv[1])

    # Uncomment to see debug output
    m.verbosity = 2

    # Set to the address of the conditonal checking for the first complex branch
    to_abandon = int(sys.argv[2], 0)

    @m.hook(to_abandon)
    def explore(state):
        print "Abandoning state at PC: ", hex(state.cpu.PC)
        state.abandon()

    print "Adding hook to: {:x}".format(to_abandon)

    m.run()
