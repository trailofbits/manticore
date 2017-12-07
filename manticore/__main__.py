import sys
import argparse

from manticore import Manticore

sys.setrecursionlimit(10000)

def parse_arguments():
    ###########################################################################
    # parse arguments
    parser = argparse.ArgumentParser(description='Dynamic binary analysis tool')
    parser.add_argument('--assertions', type=str, default=None,
                        help=argparse.SUPPRESS)
    parser.add_argument('--buffer', type=str,
                        help=argparse.SUPPRESS)
    parser.add_argument('--context', type=str, default=None,
                        help=argparse.SUPPRESS)
    parser.add_argument('--coverage', type=str, default=None,
                        help='where to write the coverage data')
    parser.add_argument('--data', type=str, default='',
                        help='Initial concrete concrete_data for the input symbolic buffer')
    # FIXME (theo) similarly to policy, add documentation here.
    disas = ['capstone', 'binja-il']
    parser.add_argument('--disasm', type=str, default='capstone', choices=disas,
                        help=argparse.SUPPRESS)
    parser.add_argument('--env', type=str, nargs=1, default=[], action='append',
                        help='Specify symbolic environment variable VARNAME=++++++')
    parser.add_argument('--file', type=str, default=[], action='append', dest='files',
                        help='Specify symbolic input file, \'+\' marks symbolic bytes')
    parser.add_argument('--names', type=str, default=None,
                        help=argparse.SUPPRESS)
    parser.add_argument('--offset', type=int, default=16,
                        help=argparse.SUPPRESS)
    # FIXME (theo) Add some documentation on the different search policy options
    parser.add_argument('--policy', type=str, default='random',
                        help=("Search policy. random|adhoc|uncovered|dicount"
                              "|icount|syscount|depth. (use + (max) or - (min)"
                              " to specify order. e.g. +random)"))
    parser.add_argument('--profile', action='store_true',
                        help='Enable profiling mode.')
    parser.add_argument('--procs', type=int, default=1,
                        help='Number of parallel processes to spawn')
    parser.add_argument('argv', type=str, nargs='+',
                        help="Path to program, and arguments ('+' in arguments indicates symbolic byte).")
    parser.add_argument('--timeout', type=int, default=0,
                        help='Timeout. Abort exploration aftr TIMEOUT seconds')
    parser.add_argument('-v', action='count', default=1,
                        help='Specify verbosity level from -v to -vvvv')
    parser.add_argument('--workspace', type=str, default=None,
                        help=("A folder name for temporaries and results."
                              "(default mcore_?????)"))
    parser.add_argument('--version', action='version', version='Manticore 0.1.5',
                         help='Show program version information')

    parsed = parser.parse_args(sys.argv[1:])
    if parsed.procs <= 0:
        parsed.procs = 1

    if parsed.policy.startswith('min'):
        parsed.policy = '-' + parsed.policy[3:]
    elif parsed.policy.startswith('max'):
        parsed.policy = '+' + parsed.policy[3:]

    return parsed


def ethereum_filename(filename):
    """

    :param str filename:
    :return:
    """
    return filename.endswith('.sol') or filename.endswith('.evm')


def ethereum_cli(args):
    from seth import ManticoreEVM, calculate_coverage, ABI

    m = ManticoreEVM(procs=args.procs)

    with open(args.argv[0]) as f:
        source_code = f.read()

    user_account = m.create_account(balance=1000)
    contract_account = m.solidity_create_contract(source_code, owner=user_account)
    attacker_account = m.create_account(balance=1000)

    last_coverage = None
    new_coverage = 0
    tx_count = 0
    while new_coverage != last_coverage and new_coverage < 100:

        symbolic_data = m.make_symbolic_buffer(320)
        symbolic_value = m.make_symbolic_value()

        m.transaction(caller=attacker_account,
                         address=contract_account,
                         data=symbolic_data,
                         value=symbolic_value )

        tx_count += 1
        last_coverage = new_coverage
        new_coverage = m.global_coverage(contract_account)

        print "[+] Coverage after %d transactions: %d%%"%(tx_count, new_coverage)
        print "[+] There are %d reverted states now"% len(m.terminated_state_ids)
        print "[+] There are %d alive states now"% len(m.running_state_ids)

    for state in m.all_states:
        print str(state.context['last_exception'])

    # for state in seth.all_states:
    #     blockchain = state.platform
    #     for tx in blockchain.transactions:  # external transactions
    #         print "Transaction:"
    #         print "\tsort %s" % tx.sort  # Last instruction or type? TBD
    #         print "\tcaller 0x%x" % state.solve_one(
    #             tx.caller)  # The caller as by the yellow paper
    #         print "\taddress 0x%x" % state.solve_one(
    #             tx.address)  # The address as by the yellow paper
    #         print "\tvalue: %d" % state.solve_one(
    #             tx.value)  # The value as by the yellow paper
    #         print "\tcalldata: %r" % state.solve_one(tx.data)
    #         print "\tresult: %s" % tx.result  # The result if any RETURN or REVERT
    #         print "\treturn_data: %r" % state.solve_one(
    #             tx.return_data)  # The returned data if RETURN or REVERT
    #
    #         if tx.sort == 'Call':
    #             metadata = seth.get_metadata(tx.address)
    #             if metadata is not None:
    #                 function_id = tx.data[:4]  # hope there is enough data
    #                 function_id = state.solve_one(function_id).encode('hex')
    #                 signature = metadata.get_func_signature(function_id)
    #                 print "\tparsed calldata", ABI.parse(signature,
    #                                                      tx.data)  # func_id, *function arguments
    #                 if tx.result == 'RETURN':
    #                     ret_types = metadata.get_func_return_types(function_id)
    #                     print '\tparsed return_data', ABI.parse(ret_types,
    #                                                             tx.return_data)  # function return
    #
    #     # the logs
    #     for log_item in blockchain.logs:
    #         print "log address", log_item.address
    #         print "memlog", log_item.memlog
    #         for topic in log_item.topics:
    #             print "topic", topic
    #
    #     for address in blockchain.deleted_addresses:
    #         print "deleted address", address  # selfdestructed address
    #
    #     # accounts alive in this state
    #     for address in blockchain.contract_accounts:
    #         code = blockchain.get_code(address)
    #         balance = blockchain.get_balance(address)
    #         trace = set((offset for address_i, offset in state.context['seth.trace'] if
    #                      address == address_i))
    #         print calculate_coverage(code, trace)  # coverage % for address in this state
    #
    #         # All accounts ever created by the script
    #         # (may not all be alife in all states)
    #         # (accounts created by contract code are not in this list )
    # print "[+] Global coverage:"
    # for address in seth.contract_accounts:
    #     print address, seth.global_coverage(
    #         address)  # coverage % for address in this state


def main():
    args = parse_arguments()

    Manticore.verbosity(args.v)

    # TODO(mark): Temporarily hack ethereum support into manticore cli
    if ethereum_filename(args.argv[0]):
        ethereum_cli(args)
        return

    env = {key:val for key, val in map(lambda env: env[0].split('='), args.env)}

    m = Manticore(args.argv[0], argv=args.argv[1:], env=env, workspace_url=args.workspace,  policy=args.policy, disasm=args.disasm)

    #Fixme(felipe) remove this, move to plugin
    m.coverage_file = args.coverage

    if args.names is not None:
        m.apply_model_hooks(args.names)

    if args.assertions:
        m.load_assertions(args.assertions)

    @m.init
    def init(initial_state):
        for file in args.files:
            initial_state.platform.add_symbolic_file(file)

    m.run(procs=args.procs, timeout=args.timeout, should_profile=args.profile)

if __name__ == '__main__':
    main()
