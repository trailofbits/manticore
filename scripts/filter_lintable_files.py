#!/usr/bin/env python3
"""
Filter Python files for linting, excluding directories that ruff excludes.
Reads file paths from stdin, outputs only files that should be linted.
"""

import os
import sys

# Directories to exclude from linting (matching ruff config)
EXCLUDED_DIRS = {
    ".tox",
    ".git",
    "docs",
    "examples",
    "scripts",
    "tests",
    "venv",
    "server",
}

# Files to exclude from linting
EXCLUDED_FILES = {
    "iterpickle.py",
}

def should_lint(filepath):
    """Check if a file should be linted."""
    if not filepath.endswith(".py"):
        return False
    
    if not os.path.exists(filepath):
        return False
    
    # Check if file is in an excluded directory
    parts = filepath.split(os.sep)
    for part in parts[:-1]:  # Exclude the filename itself
        if part in EXCLUDED_DIRS:
            return False
    
    # Check if file is explicitly excluded
    filename = os.path.basename(filepath)
    if filename in EXCLUDED_FILES:
        return False
    
    # Special case: generated files
    if filename.endswith("_pb2.py"):
        return False
    
    return True

if __name__ == "__main__":
    for line in sys.stdin:
        filepath = line.strip()
        if should_lint(filepath):
            print(filepath)