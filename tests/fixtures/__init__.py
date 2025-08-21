"""
Test fixtures and shared utilities for Manticore tests.

This module provides common test data and helper functions that can be
used across different test suites.
"""

from pathlib import Path

# Path to fixtures directory
FIXTURES_DIR = Path(__file__).parent

# Path to test root
TESTS_DIR = FIXTURES_DIR.parent

# Common paths
NATIVE_BINARIES = TESTS_DIR / "native" / "binaries"
ETHEREUM_CONTRACTS = TESTS_DIR / "ethereum" / "contracts"
ETHEREUM_DATA = TESTS_DIR / "ethereum" / "data"


def get_fixture_path(filename):
    """Get the full path to a fixture file.
    
    Args:
        filename: Name of the fixture file
        
    Returns:
        Path object to the fixture file
    """
    return FIXTURES_DIR / filename


def load_binary(binary_name):
    """Load a test binary from the native/binaries directory.
    
    Args:
        binary_name: Name of the binary file
        
    Returns:
        Bytes of the binary file
    """
    binary_path = NATIVE_BINARIES / binary_name
    if not binary_path.exists():
        raise FileNotFoundError(f"Binary not found: {binary_name}")
    return binary_path.read_bytes()