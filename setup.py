import os
from setuptools import setup, find_packages

on_rtd = os.environ.get('READTHEDOCS') == 'True'


def rtd_dependent_deps():
    # RTD tries to build z3, ooms, and fails to build.
    if on_rtd:
        return []
    else:
        return ['z3-solver']


setup(
    name='manticore',
    description='Manticore is a symbolic execution tool for analysis of binaries and smart contracts.',
    url='https://github.com/trailofbits/manticore',
    author='Trail of Bits',
    version='0.2.1.1',
    packages=find_packages(),
    python_requires='>=3.6',
    install_requires=[
        'capstone>=3.0.5',
        'pyelftools',
        'unicorn',
        'ply',
        'pysha3',
        'pyevmasm',
        'pyyaml',
    ] + rtd_dependent_deps(),
    dependency_links=[
        'https://github.com/aquynh/capstone/archive/next.zip#egg=capstone-4&subdirectory=bindings/python',
    ],
    extras_require={
        'dev': [
            'keystone-engine',
            'coverage',
            'nose',
            'Sphinx',
        ],
        'dev-noks': [
            'coverage',
            'nose',
            'Sphinx',
        ],
        'redis': [
            'redis',
        ]
    },
    entry_points={
        'console_scripts': [
            'manticore = manticore.__main__:main'
        ]
    }
)
