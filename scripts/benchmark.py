from manticore import Manticore
from sys import argv, exit
from time import time

def print_results(time_elapsed, instructions_executed):
    print "  Total time: {} seconds".format(time_elapsed)
    print "  Total instructions executed: {}".format(instructions_executed)
    print "  Average instructions per second: {}".format(instructions_executed / time_elapsed)

def benchmark(program):
    print "[*] Benchmarking program \"{}\"".format(program)
    time_started = time()

    m = Manticore(program)
    m.should_profile = True
    m.run()

    time_elapsed = time() - time_started
    instructions_executed = m._executor.count

    print_results(time_elapsed, instructions_executed)
    return(time_elapsed, instructions_executed)

if __name__ == "__main__":
    if len(argv) == 0:
        print "usage: python benchmark.py PROGRAM1 PROGRAM2..."
        exit()

    instructions_executed = 0
    time_elapsed = 0

    for program in argv[1:]:
        (seconds, instructions) = benchmark(program)
        time_elapsed += seconds
        instructions_executed += instructions
        
    print "Overall:"
    print_results(time_elapsed, instructions_executed)
