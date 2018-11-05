def contract_addr(address):
    """
    Return string indicating contact address
    """
    return F'Contract: 0x{address}'


def evm_program_counter(pc, at_init=""):
    """
    Return string indicating EVM program counter and whether counter was read
    at constructor
    """
    return F'EVM Program counter: 0x{pc}{" (at constructor)" if at_init else ""}\n'
