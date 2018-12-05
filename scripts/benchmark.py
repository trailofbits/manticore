from __future__ import print_function
from manticore.native import Manticore
from sys import argv, exit


def display(results):
    for line in str(results).split('\n'):
        print("  " + line)


def benchmark(program):
    print(f"[*] Benchmarking program \"{program}\"")

    m = Manticore(program)
    m.run(should_profile=True)

    results = m._executor.dump_stats()
    if results is None:
        print(f"[*] Failed to collect stats for program {program}")
        return

    display(results)
    return results


if __name__ == "__main__":
    args = argv[1:]

    if len(args) == 0:
        print(f"usage: python {argv[0]} PROGRAM1 PROGRAM2...")
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
