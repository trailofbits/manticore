import subprocess
import sys


def propose_install_deps():
    print('''
[*] It seems that your Manticore installation lacks targets dependencies.
[*]
[*] Choose your option:
[*] 1) get more detailed information
[*] 2) install Ethereum vm targets dependencies
[*] 3) install native targets (x86, x86-64, armv7, decree) dependencies
[*] 4) install both native and evm targets dependencies
[*] 5) exit
''')
    choice = None
    while choice not in {'1', '2', '3', '4', '5'}:
        choice = input('Your choice (1/2/3/4/5): ')

    if choice == '1':
        print('''
Since Manticore supports different targets and they have different dependencies
we decided to not install all of them.

So we use `extra_requires` in `setup.py` so people can specify what they
want to install, e.g.:
- pip install manticore[evm]        - will install evm targets dependencies
- pip install manticore[native]     - will install native targets (x86, x86-64, armv7, decree) dependencies
- pip install manticore[native,evm] - will install both native and evm targets dependencies

And those are the commands we run under the hood if you choose one of install options.

Also, this message might reappear if you try to play with the target you don't have dependencies for.
''')

    elif choice == '5':
        print('Nothing was installed. Bye!')
        sys.exit(0)
    else:

        choice2depname = {
            '2': 'evm',
            '3': 'native',
            '4': 'evm,native'
        }
        deps = choice2depname[choice]

        cmd = [sys.executable, '-m', 'pip', 'install', f'.[{deps}]']

        print(f'[*] Launching: {cmd}')

        result = subprocess.call(cmd)

        if result != 0:
            print(
                '[*] The installation failed; you might be missing some dynamic library or a compilation/build tool.\n'
                '[*] Try to investigate it on your own and if it fails, check out issues on '
                'https://github.com/trailofbits/manticore/issues or send us one.'
            )

        return result
