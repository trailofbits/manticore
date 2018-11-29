#!/usr/bin/env python3
'''
hook_injector.py

    This example harnesses the power of
    Manticore as a debugger during program analysis,
    providing introspection of hooks injected through
    user-specified pattern inputs.

'''
import re
import argparse

from manticore import Manticore
from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection


class Introspector(object):
    """
    Introspector object is used to correctly parse
    an ELF binary with a symbol table
    """

    def __init__(self, target_f, pattern):

        # collected mem addresses from symbol pattern
        self.functions = []

        # instantiate manticore with binary target
        self.mcore = Manticore(target_f)

        with open(target_f, 'rb') as binary:

            # parse binary
            elf = ELFFile(binary)
            if elf is None:
                raise Exception("symbols are unsupported")

            # retrieve symbols from all sections in binary
            for section in elf.iter_sections():

                # check if symbol table
                if not isinstance(section, SymbolTableSection):
                    continue

                # retrieve ALL symbols
                syms = section.iter_symbols()
                if syms is None:
                    raise Exception("no symbols found")

                # create dict of symbols and respective memory addr, which is represented by
                # 'st_value' attribute in symbol table entry
                symbols = dict((sym.name, sym.entry['st_value']) for sym in syms)

                # regex matching against symbols
                for name, addr in symbols.items():
                    if re.match(pattern, name):
                        self.functions.append(addr)


    def attach_and_run(self, callback):
        """
        Attach Manticore hooks to all memory addresses
        and run symbolic executor
        """
        
        for addr in self.functions:
            self.mcore.add_hook(addr, callback)

        self.mcore.verbosity = 2
        self.mcore.workers = 1
        self.mcore.run()



def main():

    # initialize parser and parse arguments 
    parser = argparse.ArgumentParser(description='Inject hooks at user-specified patterns')
    parser.add_argument('-i', '--input', type=str,
                        help="Pattern input for hook injection")
    parser.add_argument('file', type=str,
                        help="Path to binary file for introspection")
    args = parser.parse_args()

    # initialize introspection object
    introspect = Introspector(args.file, args.input)

    # define your hook callback
    def hook(state):
        cpu = state.cpu
        print('eax', cpu.EAX)

    # attach hooks and run manticore
    introspect.attach_and_run(hook)


if __name__ == '__main__':
    main()
