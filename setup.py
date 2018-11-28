import os
from setuptools import setup, find_packages

on_rtd = os.environ.get('READTHEDOCS') == 'True'


# Dependencies that the user can specify, e.g. as:
#   - pip install manticore[native]`        - install only native cpu's dependencies
#   - pip install manticore[evm]            - install evm cpu's dependencies
#   - pip install manticore[native,evm]     - install all
#
# If the user doesn't specify any of them,
# we will warn them to install dependencies when they use Manticore


def rtd_dependent_deps():
    # RTD tries to build z3, ooms, and fails to build.
    if on_rtd:
        return []
    else:
        return ['z3-solver']


extra_require = {
    'native': [
        'capstone>=3.0.5',
        'pyelftools',
        'unicorn',
    ],
    'evm': [
        'pysha3',
        # In 0.1.1, pyevmasm changed its gas cost calculations, so Manticore will need to update its
        # unit tests to match before we can upgrade pyevmasm
        'pyevmasm==0.1.0',
        'ply'
    ],
    'dev': [
        'keystone-engine',
        'coverage',
        'nose',
        'Sphinx',
    ],
    # noks - no keystone
    'dev-noks': [
        'coverage',
        'nose',
        'Sphinx',
    ],
    'redis': [
        'redis',
    ]
}

from manticore.utils.install_helper import REQUIREMENTS_TO_IMPORTS
for extra in REQUIREMENTS_TO_IMPORTS:
    setup_deps = extra_require[extra]

    def trunc(name):
        if '>' in name:
            return name[:name.index('>')]
        elif '=' in name:
            return name[:name.index('=')]
        return name

    setup_deps = set(trunc(i) for i in setup_deps)
    checked_deps = set(REQUIREMENTS_TO_IMPORTS[extra])

    if setup_deps != checked_deps:
        raise Exception(
            f'Please fix requirements for {extra} in setup.py or in utils/install_helper.py\n'
            f'In setup.py we have: {setup_deps}\n'
            f'In utils/install_helper.py we have: {checked_deps}'
        )

setup(
    name='manticore',
    description='Manticore is a symbolic execution tool for analysis of binaries and smart contracts.',
    url='https://github.com/trailofbits/manticore',
    author='Trail of Bits',
    version='0.2.2',
    packages=find_packages(exclude=['tests', 'tests.*']),
    python_requires='>=3.6',
    install_requires=['pyyaml'] + rtd_dependent_deps(),
    dependency_links=[
        'https://github.com/aquynh/capstone/archive/next.zip#egg=capstone-4&subdirectory=bindings/python',
    ],
    extras_require=extra_require,
    entry_points={
        'console_scripts': [
            'manticore = manticore.__main__:main'
        ]
    }
)
