from setuptools import setup, find_packages

setup(
    name='Manticore',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[
        'capstone',
        'pyelftools',
        'unicorn',
    ],
    extras_require={
        'dev': [
            'keystone',
            'coverage',
            'nosetests',
        ]
    },
    entry_points={
        'console_scripts': [
            'manticore = manticore.__main__:main'
        ]
    }
)