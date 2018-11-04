def contract_addr(address):
    """
    Return string indicating contact address
    """
    return 'Contract: 0x{}'.format(address)


def evm_program_counter(pc, at_init=""):
    """
    Return string indicating EVM program counter and whether counter was read
    at constructor
    """
    return 'EVM Program counter: 0x{}{}\n'.format(pc, at_init and " (at constructor)" or "")
