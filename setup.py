from setuptools import setup, find_packages

setup(
    name='manticore',
    description='Manticore is a prototyping tool for dynamic binary analysis, with support for symbolic execution, taint analysis, and binary instrumentation.',
    url='https://github.com/trailofbits/manticore',
    author='Trail of Bits',
    version='0.1.2',
    packages=find_packages(),
    install_requires=[
        'capstone>=3.0.5rc2',
        'pyelftools',
        'unicorn',
        'ply',
    ],
    extras_require={
        'dev': [
            'keystone-engine',
            'coverage',
            'nose',
            'Sphinx',
        ]
    },
    entry_points={
        'console_scripts': [
            'manticore = manticore.__main__:main'
        ]
    }
)
