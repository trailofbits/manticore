#!/usr/bin/env python3
"""
Helper script to configure Manticore's SMT solver.

This allows setting the solver via environment variable or creating a config file.
"""
import os
import sys
import shutil
import yaml


def check_solver_availability():
    """Check which solvers are available on the system."""
    solvers = {
        "z3": shutil.which("z3"),
        "yices-smt2": shutil.which("yices-smt2"),
        "cvc4": shutil.which("cvc4"),
        "boolector": shutil.which("boolector"),
    }

    available = {name: path for name, path in solvers.items() if path}
    return available


def create_solver_config(solver_name=None):
    """Create a manticore config file with the specified solver."""
    available = check_solver_availability()

    if not available:
        print("ERROR: No SMT solvers found!")
        print("Please install at least one of: z3, yices-smt2, cvc4, boolector")
        return False

    # If no solver specified, use environment variable or auto-detect
    if solver_name is None:
        solver_name = os.environ.get("MANTICORE_SOLVER", "auto")

    # Map friendly names to actual binary names
    solver_map = {
        "z3": "z3",
        "yices": "yices",
        "cvc4": "cvc4",
        "boolector": "boolector",
        "auto": "auto",
    }

    if solver_name in solver_map:
        solver_choice = solver_map[solver_name]
    else:
        print(f"Unknown solver: {solver_name}")
        print(f"Available options: {', '.join(solver_map.keys())}")
        return False

    # Create config
    config = {"smt": {"solver": solver_choice, "z3_bin": "z3"}}  # Explicitly set z3 binary path

    # If a specific solver is chosen, ensure it exists
    if solver_choice != "auto":
        binary_map = {"z3": "z3", "yices": "yices-smt2", "cvc4": "cvc4", "boolector": "boolector"}
        required_binary = binary_map.get(solver_choice)
        if required_binary not in available:
            print(
                f"ERROR: Solver '{solver_choice}' not found (looking for binary '{required_binary}')"
            )
            print(f"Available solvers: {', '.join(available.keys())}")
            return False

    # Write config file
    config_path = ".manticore.yml"
    with open(config_path, "w") as f:
        yaml.safe_dump(config, f)

    print(f"Created {config_path} with solver: {solver_choice}")
    if solver_choice == "auto":
        print(f"Auto mode will use first available: {', '.join(available.keys())}")

    return True


def create_solver_symlinks():
    """Create symlinks to make z3 available as different solver names if needed."""
    z3_path = shutil.which("z3")
    if z3_path:
        # Create symlink for z3-smt2 if it doesn't exist
        z3_smt2_path = "/usr/local/bin/z3-smt2"
        if not os.path.exists(z3_smt2_path):
            try:
                os.symlink(z3_path, z3_smt2_path)
                print(f"Created symlink: {z3_smt2_path} -> {z3_path}")
            except PermissionError:
                print(f"Warning: Could not create symlink {z3_smt2_path} (permission denied)")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Configure Manticore SMT solver")
    parser.add_argument(
        "--solver",
        choices=["z3", "yices", "cvc4", "boolector", "auto"],
        help="SMT solver to use (default: auto or $MANTICORE_SOLVER)",
    )
    parser.add_argument("--check", action="store_true", help="Check available solvers")
    parser.add_argument("--symlinks", action="store_true", help="Create solver symlinks if needed")

    args = parser.parse_args()

    if args.check:
        available = check_solver_availability()
        if available:
            print("Available solvers:")
            for name, path in available.items():
                print(f"  {name}: {path}")
        else:
            print("No SMT solvers found!")
        sys.exit(0)

    if args.symlinks:
        create_solver_symlinks()

    success = create_solver_config(args.solver)
    sys.exit(0 if success else 1)
