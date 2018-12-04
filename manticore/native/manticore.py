import logging

import elftools
import os
from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

from .state import State
from ..core.manticore import ManticoreBase
from ..core.smtlib import ConstraintSet
from ..utils import log, config
from ..utils.helpers import issymbolic

logger = logging.getLogger(__name__)
log.init_logging()

consts = config.get_group('main')


class Manticore(ManticoreBase):
    def __init__(self, path_or_state, argv=None, workspace_url=None, policy='random', **kwargs):
        """
        :param path_or_state: Path to binary or a state (object) to begin from.
        :param argv: arguments passed to the binary.
        """
        if isinstance(path_or_state, str):
            if not os.path.isfile(path_or_state):
                raise OSError(f'{path_or_state} is not an existing regular file')

            initial_state = _make_initial_state(path_or_state, argv=argv, **kwargs)
        else:
            initial_state = path_or_state

        super().__init__(initial_state, workspace_url=workspace_url, policy=policy, **kwargs)

    @classmethod
    def linux(cls, path, argv=None, envp=None, entry_symbol=None, symbolic_files=None, concrete_start='', pure_symbolic=False, stdin_size=consts.stdin_size, **kwargs):
        """
        Constructor for Linux binary analysis.

        :param str path: Path to binary to analyze
        :param argv: Arguments to provide to the binary
        :type argv: list[str]
        :param envp: Environment to provide to the binary
        :type envp: dict[str, str]
        :param entry_symbol: Entry symbol to resolve to start execution
        :type envp: str
        :param symbolic_files: Filenames to mark as having symbolic input
        :type symbolic_files: list[str]
        :param str concrete_start: Concrete stdin to use before symbolic input
        :param int stdin_size: symbolic stdin size to use
        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a Linux State
        :rtype: Manticore
        """
        try:
            return cls(_make_linux(path, argv, envp, entry_symbol, symbolic_files, concrete_start, pure_symbolic, stdin_size), **kwargs)
        except elftools.common.exceptions.ELFError:
            raise Exception(f'Invalid binary: {path}')

    @classmethod
    def decree(cls, path, concrete_start='', **kwargs):
        """
        Constructor for Decree binary analysis.

        :param str path: Path to binary to analyze
        :param str concrete_start: Concrete stdin to use before symbolic input
        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a Decree State
        :rtype: Manticore
        """
        try:
            return cls(_make_decree(path, concrete_start), **kwargs)
        except KeyError:  # FIXME(mark) magic parsing for DECREE should raise better error
            raise Exception(f'Invalid binary: {path}')

    #############################################################################
    #############################################################################
    #############################################################################
    # Move all the following elsewhere Not all manticores have this
    def _get_symbol_address(self, symbol):
        '''
        Return the address of |symbol| within the binary
        '''

        # XXX(yan) This is a bit obtuse; once PE support is updated this should
        # be refactored out
        if self._binary_type == 'ELF':
            self._binary_obj = ELFFile(open(self._binary, 'rb'))

        if self._binary_obj is None:
            return NotImplementedError("Symbols aren't supported")

        for section in self._binary_obj.iter_sections():
            if not isinstance(section, SymbolTableSection):
                continue

            symbols = section.get_symbol_by_name(symbol)
            if not symbols:
                continue

            return symbols[0].entry['st_value']


def _make_initial_state(binary_path, **kwargs):
    with open(binary_path, 'rb') as f:
        magic = f.read(4)
    if magic == b'\x7fELF':
        # Linux
        state = _make_linux(binary_path, **kwargs)
    elif magic == b'\x7fCGC':
        # Decree
        state = _make_decree(binary_path, **kwargs)
    else:
        raise NotImplementedError(f"Binary {binary_path} not supported.")
    return state


def _make_decree(program, concrete_start='', **kwargs):
    from ..platforms import decree

    constraints = ConstraintSet()
    platform = decree.SDecree(constraints, program)
    initial_state = State(constraints, platform)
    logger.info('Loading program %s', program)

    if concrete_start != '':
        logger.info(f'Starting with concrete input: {concrete_start}')
    platform.input.transmit(concrete_start)
    platform.input.transmit(initial_state.symbolicate_buffer('+' * 14, label='RECEIVE'))
    return initial_state


def _make_linux(program, argv=None, env=None, entry_symbol=None, symbolic_files=None, concrete_start='', pure_symbolic=False, stdin_size=consts.stdin_size):
    from ..platforms import linux

    env = {} if env is None else env
    argv = [] if argv is None else argv
    env = [f'{k}={v}' for k, v in env.items()]

    logger.info('Loading program %s', program)

    constraints = ConstraintSet()
    platform = linux.SLinux(program, argv=argv, envp=env,
                            symbolic_files=symbolic_files,
                            pure_symbolic=pure_symbolic)
    if entry_symbol is not None:
        entry_pc = platform._find_symbol(entry_symbol)
        if entry_pc is None:
            logger.error("No symbol for '%s' in %s", entry_symbol, program)
            raise Exception("Symbol not found")
        else:
            logger.info("Found symbol '%s' (%x)", entry_symbol, entry_pc)
            #TODO: use argv as arguments for function
            platform.set_entry(entry_pc)

    initial_state = State(constraints, platform)

    if concrete_start != '':
        logger.info('Starting with concrete input: %s', concrete_start)

    if pure_symbolic:
        logger.warning('[EXPERIMENTAL] Using purely symbolic memory.')

    for i, arg in enumerate(argv):
        argv[i] = initial_state.symbolicate_buffer(arg, label=f'ARGV{i + 1}')

    for i, evar in enumerate(env):
        env[i] = initial_state.symbolicate_buffer(evar, label=f'ENV{i + 1}')

    # If any of the arguments or environment refer to symbolic values, re-
    # initialize the stack
    if any(issymbolic(x) for val in argv + env for x in val):
        platform.setup_stack([program] + argv, env)

    platform.input.write(concrete_start)

    # set stdin input...
    platform.input.write(initial_state.symbolicate_buffer('+' * stdin_size,
                                                          label='STDIN'))
    return initial_state
