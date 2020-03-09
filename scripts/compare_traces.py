import sys

import os


def compare_traces(dir1: str, dir2: str):
    """
    Compare state traces from two mcore_* directories.

    For now assumes to use `test_xxxxxxx.trace` only.
    """
    get_traces = lambda dir: [
        f for f in os.listdir(dir) if f.startswith("test_") and f.endswith(".trace")
    ]

    traces1 = get_traces(dir1)
    traces2 = get_traces(dir2)

    traces1.sort()
    traces2.sort()

    print("### Comparing traces: ")
    print(f"dir1 - {dir1} :")
    print(", ".join(traces1))
    print()
    print(f"dir2 - {dir2} :")
    print(", ".join(traces2))

    for t1, t2 in zip(traces1, traces2):
        path1 = os.path.join(dir1, t1)
        path2 = os.path.join(dir2, t2)

        with open(path1) as fp1, open(path2) as fp2:
            if fp1.read() != fp2.read():
                print(f"Files {t1} and {t2} differs.")
            else:
                print(f"Files {t1} and {t2} matches.")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} MCORE_DIR_1 MCORE_DIR_2")
        sys.exit()

    dir1, dir2 = sys.argv[1:]

    not_dir = lambda d: not os.path.isdir(d)

    if not_dir(dir1) or not_dir(dir2):
        print("One of passed args is not a directory!")
        sys.exit(-1)

    compare_traces(dir1, dir2)
