"""
Utilities for solver configuration and selection.
"""

from ..core.smtlib.solver import (
    PortfolioSolver,
    SelectedSolver,
    SolverType,
)
from . import config


def get_solver_instance():
    """
    Get a solver instance based on configuration.

    This function respects the SMT solver configuration and returns:
    - PortfolioSolver if explicitly configured
    - The configured solver otherwise (auto, z3, yices, etc.)

    Returns:
        A solver instance appropriate for the current configuration.
    """
    consts = config.get_group("smt")

    if consts.solver == SolverType.portfolio:
        # User explicitly wants portfolio solver
        return PortfolioSolver.instance()
    else:
        # Use the configured solver (auto will pick the first available)
        return SelectedSolver.instance()


def is_portfolio_solver_configured():
    """
    Check if the portfolio solver is configured.

    Returns:
        bool: True if portfolio solver is configured, False otherwise.
    """
    consts = config.get_group("smt")
    return consts.solver == SolverType.portfolio
