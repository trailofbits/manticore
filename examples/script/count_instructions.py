
import sys
from manticore import Manticore

'''
Count the number of emulated instructions.

This uses the ability of the Manticore object to act as a dict to store data
that is used/updated in the hook function.

'''

if __name__ == '__main__':
    if len(sys.argv) < 2:
        sys.stderr.write("Usage: %s [binary]\n"%(sys.argv[0],))
        sys.exit(2)

    m = Manticore(sys.argv[1])
    m.workers = 3

    m['count'] = 0

    def explore(state):
        m['count'] += 1

    m.add_hook(None, explore)

    m.start()

    print "Executed ", m['count'], " instructions."
