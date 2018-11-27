import subprocess
import sys
import pkg_resources


REQUIREMENTS_TO_IMPORTS = {
    'evm': {
        'pysha3': 'sha3',
        'pyevmasm': 'pyevmasm',
        'ply': 'ply'
    },
    'native': {
        'capstone': 'capstone',
        'pyelftools': 'elftools',
        'unicorn': 'unicorn'
    }
}


def ensure_any_deps():
    if not _has_evm and not _has_native:
        _propose_install_deps()


def ensure_evm_deps():
    if not _has_evm:
        _propose_install_deps()


def ensure_native_deps():
    if not _has_native:
        _propose_install_deps()


def _has_deps(deps):
    for pkg, import_name in REQUIREMENTS_TO_IMPORTS[deps].items():
        try:
            __import__(import_name)
        except ImportError:
            return False

    return True


_has_native = _has_deps('native')
_has_evm = _has_deps('evm')


def _propose_install_deps():
    print(f'''
[*] It seems that your Manticore installation lacks targets dependencies.
[*]
[*] Choose your option:
[*] 1) get more detailed information
[*] 2) install Ethereum vm target dependencies{' (installed)' if _has_evm else ''}
[*] 3) install native targets (x86, x86-64, armv7, decree) dependencies{' (installed)' if _has_native else ''}
[*] 4) install both native and evm targets dependencies
[*] 5) exit
''')
    choice = None
    while choice not in {'1', '2', '3', '4', '5'}:
        choice = input('Your choice (1/2/3/4/5): ')

    if choice == '1':
        print('''
Since Manticore supports different targets and they have different dependencies
we decided not to install all of them when `pip install manticore` is invoked.

Instead, we use `extra_requires` in `setup.py` so it is possible to specify
the dependencies to be installed with pip, e.g.:
- pip install manticore[evm]        - will install evm target dependencies
- pip install manticore[native]     - will install native targets (x86, x86-64, armv7, decree) dependencies
- pip install manticore[native,evm] - will install both native and evm targets dependencies

And those are the commands we run under the hood if you choose one of install options.

Also, this message might reappear if you try to play with the target you don't have dependencies for.
''')

    elif choice == '5':
        print('Nothing was installed. Bye!')
    else:

        choice2depname = {
            '2': 'evm',
            '3': 'native',
            '4': 'evm,native'
        }
        deps = choice2depname[choice]

        # We need to use (proper) `manticore==<version>` here
        version = pkg_resources.get_distribution('manticore').version

        cmd = [sys.executable, '-m', 'pip', 'install', f'manticore[{deps}]=={version}']

        print(f'[*] Launching: {cmd}')

        result = subprocess.call(cmd)

        if result != 0:
            print(
                '[*] The installation failed; you might be missing some dynamic library or a compilation/build tool.\n'
                '[*] Try to investigate it on your own and if it fails, check out issues on '
                'https://github.com/trailofbits/manticore/issues or send us one.'
            )

        sys.exit(result)

    sys.exit(0)
