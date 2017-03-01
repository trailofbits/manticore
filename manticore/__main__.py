import sys
import os
import argparse
import logging
import time
import types
import cPickle
from multiprocessing import Manager, Pool, Process
from threading import Timer
from core.smtlib import Expression
from manticore import Manticore
try:
    import psutil
except ImportError:
    pass
sys.setrecursionlimit(10000)


def parse_arguments():
    ###########################################################################
    # parse arguments
    parser = argparse.ArgumentParser(description='Symbolically analyze a program')
    parser.add_argument('--workspace', type=str, default=None,
                        help='A folder name for temporaries and results. (default mcore_?????)')
    parser.add_argument('--log', type=str, default='-',
                        help='The log filename')
    parser.add_argument('--verbose', action='store_true', help='Enable debug mode.')
    parser.add_argument('--profile', action='store_true', help='Enable profiling mode.')

    parser.add_argument('--buffer', type=str, help='Specify buffer to make symbolic')
    parser.add_argument('--size', type=str, help='Specify buffer full size')
    parser.add_argument('--offset', type=int, default=16, help='Buffer header size to leave concrete')
    parser.add_argument('--maxsymb', type=int, default=512, help='Maximun number of symbolic bytes to inject')
    parser.add_argument('--data', type=str, default='',
                        help='Initial concrete concrete_data for the input symbolic buffer')
    parser.add_argument('--env', type=str, nargs='+', default=[],
                        help='Specify symbolic environment variable VARNAME=++++++')
    parser.add_argument('--policy', type=str, default='random',
                        help='Search policy. random|adhoc|uncovered|dicount|icount|syscount|depth.'\
                             ' (use + (max) or - (min) to specify order. e.g. +random)')
    parser.add_argument('--dumpafter', type=int, default=0, help='Dump state after every N instructions; 0 to disable')
    parser.add_argument('--maxstorage', type=int, default=0, help='Storage use cap in megabytes.')
    parser.add_argument('--maxstates', type=int, default=0, help='Maximun number of states to mantain at the same time')
    parser.add_argument('--procs', type=int, default=1, choices=xrange(1, 20), help='Number of parallel workers to spawn')
    parser.add_argument('--timeout', type=int, default=0, help='Timeout. Abort exploration aftr TIMEOUT seconds')
    parser.add_argument('--replay', type=str, default=None,
                       help='The trace filename to replay')
    parser.add_argument('--coverage', type=str, default=None,
                        help='where to write the coverage data')
    parser.add_argument('--errorfile', type=str, default=None,
                        help='where to write the memory error locations')
    parser.add_argument('--context', type=str, default=None, help='path to file with additional context')
    parser.add_argument('--assertions', type=str, default=None, help='File with additional assertions')
    parser.add_argument('--names', type=str, default=None, help='File with function addresses to replace with known models')
    parser.add_argument('programs', type=str, nargs='+', metavar='PROGRAM',
                       help='Programs to analyze (arguments after ?)' )
    parser.add_argument('--no-mp', action='store_true', help='Disable multiprocess')

    parsed = parser.parse_args(sys.argv[1:])
    if parsed.procs <= 0 :
        parsed.procs = 1

    if parsed.policy.startswith('min'):
        parsed.policy = '-'+parsed.policy[3:]
    elif parsed.policy.startswith('max'):
        parsed.policy = '+'+parsed.policy[3:]

    return parsed


logger = logging.getLogger('MAIN')

def main():
    args = parse_arguments()

    m = Manticore(args.programs[0], args.programs[1:])

    m.policy = args.policy
    m.args = args

    if args.workspace:
        m.workspace = args.workspace

    if args.log:
        m.log_file = args.log

    if args.profile:
        m.should_profile = args.profile

    if args.dumpafter != 0:
        m.dumpafter = args.dumpafter

    if args.maxstorage != 0:
        m.maxstorage = args.maxstorage

    if args.maxstates != 0:
        m.maxstates = args.maxstates

    if args.coverage:
        m.coverage_file = args.coverage

    if args.names is not None:
        m.apply_model_hooks(args.names)

    if args.procs:
        m.workers = args.procs

    if args.env:
        for entry in args.env:
            name, val = entry.split('=')
            m.env_add(name, val)

    if args.assertions:
        m.load_assertions(args.assertions)

    # logging
    class ContextFilter(logging.Filter):
        '''
        This is a filter which injects contextual information into the log.
        '''
        def filter(self, record):
            if hasattr(self, 'stateid') and isinstance(self.stateid, int):
                record.stateid = '[%d]' % self.stateid
            else:
                record.stateid = ''
            return True
    
    
    def loggerSetState(logger, stateid):
        logger.filters[0].stateid = stateid

    logging.basicConfig(filename = args.log,
                        format = '%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s: %(message)s',
                        level = {False:logging.INFO, True:logging.DEBUG}[args.verbose])

    verbosity = {False:logging.INFO, True:logging.DEBUG}[args.verbose]
    ctxfilter = ContextFilter()

    for loggername in ['VISITOR', 'EXECUTOR', 'CPU', 'SMT', 'MEMORY', 'MAIN', 'MODEL']:
        logging.getLogger(loggername).addFilter(ctxfilter)
        logging.getLogger(loggername).setLevel(verbosity)
        logging.getLogger(loggername).setState = types.MethodType(loggerSetState, logging.getLogger(loggername))

    logging.getLogger('SMT').setLevel(logging.INFO)
    logging.getLogger('MEMORY').setLevel(logging.INFO)
    #logging.getLogger('CPU').setLevel(logging.INFO)
    logging.getLogger('LIBC').setLevel(logging.INFO)

    logger.info('[+] Loading challenge %s', args.programs)

    m.run()

    m.dump_stats()

if __name__ == '__main__':
    main()
