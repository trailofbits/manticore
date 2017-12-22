from setuptools import setup, find_packages

setup(
    name='manticore',
    description='Manticore is a symbolic execution tool for analysis of binaries and smart contracts.',
    url='https://github.com/trailofbits/manticore',
    author='Trail of Bits',
    version='0.1.6',
    packages=find_packages(),
    install_requires=[
        'capstone>=3.0.5rc2',
        'pyelftools',
        'unicorn',
        'ply',
        'pysha3',
        'z3-solver',
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
