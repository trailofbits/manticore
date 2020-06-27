import os
import sys
from setuptools import setup, find_packages
from datetime import date

on_rtd = os.environ.get("READTHEDOCS") == "True"


def rtd_dependent_deps():
    # RTD tries to build z3, ooms, and fails to build.
    if on_rtd:
        return native_deps
    else:
        return ["z3-solver"]


# If you update native_deps please update the `REQUIREMENTS_TO_IMPORTS` dict in `utils/install_helper.py`
# (we need to know how to import a given native dependency so we can check if native dependencies are installed)
native_deps = ["capstone==4.0.1", "pyelftools", "unicorn==1.0.2rc2"]

lint_deps = ["black==19.10b0", "mypy==0.770"]

auto_test_deps = ["py-evm"]

# Development dependencies without keystone
dev_noks = (
    native_deps
    + ["coverage", "Sphinx", "pytest==5.3.0", "pytest-xdist==1.30.0", "pytest-cov==2.8.1", "jinja2"]
    + lint_deps
    + auto_test_deps
)

extra_require = {
    "native": native_deps,
    # noks - no keystone
    "dev-noks": dev_noks,
    "dev": native_deps + dev_noks + ["keystone-engine"],
    "redis": ["redis"],
    "lint": lint_deps,
}

this_directory = os.path.abspath(os.path.dirname(__file__))
with open(os.path.join(this_directory, "README.md"), encoding="utf-8") as f:
    long_description = f.read()


# https://stackoverflow.com/a/4792601 grumble grumble
dev_extension = ""
if "--dev_release" in sys.argv:
    dev_extension = ".dev" + date.today().strftime("%y%m%d")
    sys.argv.remove("--dev_release")

setup(
    name="manticore",
    description="Manticore is a symbolic execution tool for analysis of binaries and smart contracts.",
    long_description_content_type="text/markdown",
    long_description=long_description,
    url="https://github.com/trailofbits/manticore",
    author="Trail of Bits",
    version="0.3.4" + dev_extension,
    packages=find_packages(exclude=["tests", "tests.*"]),
    python_requires=">=3.6",
    install_requires=[
        "pyyaml",
        "pysha3",
        "prettytable",
        "ply",
        "rlp",
        "crytic-compile>=0.1.1",
        "wasm",
        "dataclasses; python_version < '3.7'",
        "pyevmasm>=0.2.3",
    ]
    + rtd_dependent_deps(),
    extras_require=extra_require,
    entry_points={
        "console_scripts": [
            "manticore = manticore.__main__:main",
            "manticore-verifier = manticore.ethereum.verifier:main",
        ]
    },
    classifiers=["License :: OSI Approved :: GNU Affero General Public License v3"],
)
