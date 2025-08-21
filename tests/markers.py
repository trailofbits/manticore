"""
Test markers and categories for better test organization.

This module provides decorators and utilities to mark tests by type,
making it easier to run specific categories of tests.

Usage:
    from tests.markers import integration_test, slow_test, unit_test
    
    @unit_test
    def test_something():
        pass
    
    @integration_test
    @slow_test
    def test_complex_workflow():
        pass

Run specific categories:
    pytest -m "not slow_test"  # Skip slow tests
    pytest -m integration_test  # Only integration tests
"""

import pytest

# Test category markers
unit_test = pytest.mark.unit
integration_test = pytest.mark.integration
slow_test = pytest.mark.slow
fast_test = pytest.mark.fast
linux_only = pytest.mark.linux
requires_network = pytest.mark.network

# Component markers  
ethereum_test = pytest.mark.ethereum
native_test = pytest.mark.native
wasm_test = pytest.mark.wasm

# Special markers
generated_test = pytest.mark.generated  # For auto-generated tests
benchmark = pytest.mark.benchmark


def mark_generated_tests(test_class):
    """Decorator to mark all tests in a class as generated.
    
    Use this for test classes containing auto-generated tests.
    """
    for attr_name in dir(test_class):
        if attr_name.startswith('test_'):
            attr = getattr(test_class, attr_name)
            setattr(test_class, attr_name, generated_test(attr))
    return test_class