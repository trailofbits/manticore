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
    version='0.1.10',
    packages=find_packages(),
    install_requires=[
        'capstone>=3.0.5rc2',
        'pyelftools',
        'unicorn',
        'ply',
        'pysha3',
        'functools32',
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
            'redis',
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
