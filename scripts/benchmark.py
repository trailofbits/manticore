from __future__ import print_function
from manticore import Manticore
from sys import argv, exit

def display(results):
    for line in str(results).split('\n'):
        print("  " + line)

def benchmark(program):
    print("[*] Benchmarking program \"{}\"".format(program))

    m = Manticore(program)
    m.should_profile = True
    m.run()

    results = m._executor.dump_stats()
    if results is None:
        print("[*] Failed to collect stats for program {}".format(program))
        return

    display(results)
    return results

if __name__ == "__main__":
    args = argv[1:]

    if len(args) == 0:
        print("usage: python {} PROGRAM1 PROGRAM2...".format(argv[0]))
        exit()

    first_program = args[0]
    other_programs = args[1:]
    overall_results = benchmark(first_program)

    if other_programs:
        for program in other_programs:
            results = benchmark(program)
            overall_results.time_elapsed += results.time_elapsed
            overall_results.instructions_executed += results.instructions_executed
            overall_results.solver_time += results.solver_time
            overall_results.loading_time += results.loading_time
            overall_results.saving_time += results.saving_time
            
        print("Overall:")
        display(overall_results)
