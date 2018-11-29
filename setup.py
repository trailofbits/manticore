import os
from setuptools import setup, find_packages

on_rtd = os.environ.get('READTHEDOCS') == 'True'


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


setup(
    name='manticore',
    description='Manticore is a symbolic execution tool for analysis of binaries and smart contracts.',
    url='https://github.com/trailofbits/manticore',
    author='Trail of Bits',
    version='0.2.2',
    packages=find_packages(exclude=['tests', 'tests.*']),
    python_requires='>=3.6',
    install_requires=[
        'pyyaml',
        # evm dependencies
        'pysha3',
        # In 0.1.1, pyevmasm changed its gas cost calculations, so Manticore will need to update its
        # unit tests to match before we can upgrade pyevmasm
        'pyevmasm==0.1.0',
        'ply'
    ] + rtd_dependent_deps(),
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
