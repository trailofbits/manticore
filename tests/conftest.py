import pytest

from manticore.utils import log


@pytest.fixture(scope="session", autouse=True)
def initialize_manticore_logging(request):
    """Initialize Manticore's logger for all tests"""
    log.init_logging()
