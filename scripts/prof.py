"""
Script used to profile Manticore runs.
"""

from __future__ import print_function

from sys import argv, exit

from manticore.native import Manticore
from manticore.core.plugin import Profiler


def profile(program, sort="cumulative"):
    print(f'[*] Profiling program "{program}"')

    m = Manticore(program)
    profiler = Profiler()
    m.register_plugin(profiler)
    m.run()
    m.finalize()

    stats = profiler.get_profiling_data()
    print(f"[*] Loaded profiling data.")

    if stats is None:
        print(f"[*] Failed to collect stats for program {program}")
        return

    stats.sort_stats(sort)

    stats.print_stats()


if __name__ == "__main__":
    if len(argv) != 2:
        print(f"usage: python {argv[0]} PROGRAM [SORT_METHOD]")
        print("The default SORT_METHOD is cumulative")
        print(
            "SORT_METHODs can be seen on https://docs.python.org/3/library/profile.html#pstats.Stats.sort_stats"
        )
        exit()

    profile(argv[1])
