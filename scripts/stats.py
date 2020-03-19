import sys, os, pickle, argparse


# Process the data of a workspace and prints out some global information


def parse_arguments():
    ################################################################################
    # parse arguments
    parser = argparse.ArgumentParser(
        description="Extract different statistic and information from a manticore workspace"
    )
    parser.add_argument(
        "--workspace",
        type=str,
        default=None,
        help="A folder name for temporaries and results. (default mcore_?????)",
    )
    parser.add_argument("--pcfreq", action="store_true", help="Print out visited pc and frequency")
    parser.add_argument("--visited", action="store_true", help="Print out visited pc set")
    parser.add_argument("--bbs", action="store_true", help="Print out visited basic blocks ")

    parser.add_argument(
        "workspace",
        type=str,
        nargs=1,
        metavar="WORKSPACE",
        help="The folder name for temporaries and results",
    )
    parsed = parser.parse_args(sys.argv[1:])
    parsed.workspace = parsed.workspace[0]

    assert (
        int(parsed.pcfreq) + int(parsed.visited) + int(parsed.bbs) == 1
    ), "Choose one option from: --pcfreq --visited"
    return parsed


args = parse_arguments()
workspace = args.workspace

# search previously generated states
saved_states = [
    os.path.join(workspace, filename)
    for filename in os.listdir(workspace)
    if filename.endswith(".pkl")
]
# prepare a dictionary to hold states
db = {}
edges = {}
for filename in saved_states:
    try:
        with open(filename, "rb") as f:
            # load the whole saved state (memory/cpu/solver/..)
            state = pickle.loads(f.read())
            lastpc = "ROOT"
            for proc, pc in state.visited:
                assert proc == 0, "Multi process no supported"
                db[pc] = db.setdefault(pc, 0) + 1
                edges.setdefault(lastpc, []).append(pc)
                lastpc = pc
    except Exception as e:
        print(f"#Failed to load saved state {filename} ({str(e)})")

if args.pcfreq:
    print("#PC:  frequency")
    for pc, freq in sorted(list(db.items()), key=lambda x: -x[1]):
        print(f"{pc:x}: {freq}")
elif args.visited:
    print("#PC")
    for pc in list(db.keys()):
        print(f"{pc:x}")
elif args.bbs:
    assert len(set(edges["ROOT"])) == 1, "Something is wrong; there should be only one root"
    bbs = set()
    for targets in list(edges.values()):
        if len(set(targets)) > 1:
            [bbs.add(x) for x in set(targets)]
    bbs.add("ROOT")
    print("#BBs")
    for origin in bbs:
        if origin not in edges:
            targets = set()
        else:
            targets = set(edges[origin])
            while len(targets) == 1:
                node = list(targets)[0]
                if node in edges:
                    targets = set(edges[node])
                else:
                    targets = ["END"]
                    break

        def p(x):
            return hex(x) if isinstance(x, int) else x

        print(f'{p(origin)} -> [{", ".join(map(p, targets))}]')
