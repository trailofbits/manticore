import os
from setuptools import setup, find_packages

on_rtd = os.environ.get("READTHEDOCS") == "True"


def rtd_dependent_deps():
    # RTD tries to build z3, ooms, and fails to build.
    if on_rtd:
        return native_deps
    else:
        return ["z3-solver"]


# If you update native_deps please update the `REQUIREMENTS_TO_IMPORTS` dict in `utils/install_helper.py`
# (we need to know how to import a given native dependency so we can check if native dependencies are installed)
native_deps = ["capstone==4.0.1", "pyelftools", "unicorn==1.0.2rc1"]

# Development dependencies without keystone
dev_noks = native_deps + [
    "coverage",
    "Sphinx",
    "black==19.3b0",
    "mypy==0.740",
    "pytest",
    "pytest-xdist",
]

extra_require = {
    "native": native_deps,
    # noks - no keystone
    "dev-noks": dev_noks,
    "dev": native_deps + dev_noks + ["keystone-engine"],
    "redis": ["redis"],
}


setup(
    name="manticore",
    description="Manticore is a symbolic execution tool for analysis of binaries and smart contracts.",
    url="https://github.com/trailofbits/manticore",
    author="Trail of Bits",
    version="0.3.2",
    packages=find_packages(exclude=["tests", "tests.*"]),
    python_requires=">=3.6",
    install_requires=[
        "pyyaml",
        "wrapt",
        # evm dependencies
        "pysha3",
        "prettytable",
        "pyevmasm==0.2.0",
        "rlp",
        "ply",
        "crytic-compile>=0.1.1",
        "wasm",
        "dataclasses; python_version < '3.7'",
    ]
    + rtd_dependent_deps(),
    extras_require=extra_require,
    entry_points={"console_scripts": ["manticore = manticore.__main__:main"]},
)
