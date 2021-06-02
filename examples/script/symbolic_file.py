#!/usr/bin/env python

"""
Example to show usage of introducing a file with symbolic contents

This script should be the equivalent of:
    $ echo "+++++++++++++" > symbolic_file.txt
    $ manticore -v --file symbolic_file.txt ../linux/fileio symbolic_file.txt
"""
import copy
import glob
import os
import pathlib
import sys
import tempfile

from manticore.__main__ import main


def test_symbolic_file(tmp_path):
    # Run this file with Manticore
    filepath = pathlib.Path(__file__).resolve().parent.parent / pathlib.Path("linux/fileio")
    assert filepath.exists(), f"Please run the Makefile in {filepath.parent} to build {filepath}"

    # Temporary workspace for Manticore
    workspace_dir = tmp_path / "mcore_workspace"
    workspace_dir.mkdir(parents=True, exist_ok=True)
    assert (
        len(os.listdir(workspace_dir)) == 0
    ), f"Manticore workspace {workspace_dir} should be empty before running"

    # Manticore will search for and read this partially symbolic file
    sym_file_name = "symbolic_file.txt"
    sym_file = tmp_path / sym_file_name
    sym_file.write_text("+++++++++++++")

    # Program arguments that would be passed to Manticore via CLI
    manticore_args = [
        # Show some progress
        "-v",
        # Register our symbolic file with Manticore
        "--file",
        str(sym_file),
        # Setup workspace, for this test, or omit to use current directory
        "--workspace",
        str(workspace_dir),
        # Manticore will execute our file here with arguments
        str(filepath),
        str(sym_file),
    ]

    # Bad hack to workaround passing the above arguments like we do on command
    # line and have them parsed with argparse
    backup_argv = copy.deepcopy(sys.argv[1:])
    del sys.argv[1:]
    sys.argv.extend(manticore_args)

    # Call Manticore's main with our new argv list for argparse
    main()

    del sys.argv[1:]
    sys.argv.extend(backup_argv)

    # Manticore will write out the concretized contents of our symbolic file for
    # each path in the program
    all_concretized_sym_files = glob.glob(str(workspace_dir / f"*{sym_file_name}"))
    assert (
        len(all_concretized_sym_files) > 1
    ), "Should have found more than 1 path through the program"
    assert any(
        map(lambda f: b"open sesame" in pathlib.Path(f).read_bytes(), all_concretized_sym_files)
    ), "Could not find 'open sesame' in our concretized symbolic file"


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as workspace:
        test_symbolic_file(pathlib.Path(workspace))
