
import sys
from manticore import Manticore

if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.stderr.write("Usage: %s [binary] [address]\n"%(sys.argv[0],))
        sys.exit(2)

    m = Manticore(sys.argv[1])

    # Set to the address of the conditonal checking for the first complex branch
    to_abandon = int(sys.argv[2], 0)

    def explore(state):
        print "Abandoning state at PC: ", hex(state.cpu.PC)
        state.abandon()

    print "Adding hook to: ", hex(to_abandon)
    m.add_hook(to_abandon, explore)

    m.run()
