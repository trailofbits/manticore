def contract_addr(address):
    """
    Return string indicating contact address
    """
    return f'Contract: 0x{address}'


def evm_program_counter(pc, at_init=""):
    """
    Return string indicating EVM program counter and whether counter was read
    at constructor
    """
    return f'EVM Program counter: 0x{pc}{at_init and " (at constructor)" or ""}\n'
