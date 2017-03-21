from manticore import Manticore
from sys import argv, exit

class Results(object):
    def __init__(self, time_elapsed, instructions_executed, loading_time, saving_time, solver_time):
        self.time_elapsed = time_elapsed
        self.instructions_executed = instructions_executed
        self.loading_time = loading_time
        self.saving_time = saving_time
        self.solver_time = solver_time

    def display(self):
        print "  Total time: {} seconds".format(self.time_elapsed)
        print "  Total instructions executed: {}".format(self.instructions_executed)
        print "  Average instructions per second: {}".format(self.instructions_executed / self.time_elapsed)
        print "  Time spent loading states: {} seconds".format(self.loading_time)
        print "  Time spent saving states: {} seconds".format(self.saving_time)
        print "  Time spent in solver: {} seconds".format(self.solver_time)

def benchmark(program):
    print "[*] Benchmarking program \"{}\"".format(program)

    m = Manticore(program)
    m.should_profile = True
    m.run()

    instructions_executed = m._executor.count
    ps = m._executor.dump_stats()
    if ps is None:
        print "[*] Failed to collect stats for program {}".format(program)
        return

    time_elapsed = ps.total_tt

    loading_time = 0
    saving_time = 0
    solver_time = 0
    for (func_file, _, func_name), (_, _, _, func_time, _) in ps.stats.iteritems():
        if func_name == '_getState':
            loading_time += func_time
        elif func_name == '_putState':
            saving_time += func_time
        elif func_file.endswith('solver.py') and 'setstate' not in func_name and 'getstate' not in func_name and 'ckl' not in func_name:
            solver_time += func_time

    results = Results(time_elapsed, instructions_executed, loading_time, saving_time, solver_time)

    results.display()
    return results

if __name__ == "__main__":
    args = argv[1:]

    if len(args) == 0:
        print "usage: python {} PROGRAM1 PROGRAM2...".format(argv[0])
        exit()

    overall_results = Results(0, 0, 0, 0, 0)

    for program in args:
        results = benchmark(program)
        overall_results.time_elapsed += results.time_elapsed
        overall_results.instructions_executed += results.instructions_executed
        overall_results.loading_time += results.loading_time
        overall_results.saving_time += results.saving_time
        overall_results.solver_time += results.solver_time
        
    print "Overall:"
    overall_results.display()
