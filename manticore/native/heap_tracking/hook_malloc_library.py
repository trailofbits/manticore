from manticore.native.state import State
from manticore.native import Manticore
from manticore.native.heap_tracking.malloc_lib_data import MallocLibData

import logging

logger = logging.getLogger(__name__)
logger.setLevel(2)


# Globals that will become class members to control amount of information being retrieved 
# TODO(Sonya): fine tune these a little bit - need to be automated
HOOK_SBRK_INFO = True
HOOK_MMAP_INFO = True
HOOK_MALLOC_RETURN = True
HOOK_FREE_RETURN = True
"""
TODO(Sonya): class conversion 
class hook_malloc_library:
    def __init__(self, m: Manticore, sbrk:int, mmap:int, munmap:int, malloc:int, free:int, calloc=None, realloc=None, 
        HOOK_SBRK_INFO: bool = True, HOOK_MMAP_INFO: bool = True, HOOK_MALLOC_RETURN: bool = True, HOOK_FREE_RETURN: bool = True):
        self.sbrk = sbrk
        self.mmap = mmap
        self.munmap = munmap
        self.malloc = malloc
        self.free = free
        
"""


def load_ret_addr(func: str, state: State):
    """ Loads the return address of a function from the stack
    (Assuming the next instruction to be executed is the start of a function call)
    """
    stack_location = state.cpu.read_register("RSP")
    ret_addr = state.cpu.read_int(stack_location, state.cpu.address_bit_size)
    logger.debug(f"Adding a hook for {func} callsite in state: {state.id}")
    return ret_addr


def hook_malloc_lib(initial_state: State, sbrk: int, mmap: int, munmap: int, malloc: int, free: int):
    """ Function to add malloc hooks and do prep work
    - TODO(Sonya): would like this to eventially be __init__() method for a class
    once manticore hook callbacks have been debugged.
    (from Eric) See: https://github.com/trailofbits/manticore/blob/master/tests/native/test_state.py#L163-L218
    & https://github.com/trailofbits/manticore/blob/master/tests/native/test_state.py#L274-L278 to work on debugging this
    """
    initial_state.context["malloc_lib"] = MallocLibData()
    
    # Hook malloc and free
    initial_state.add_hook(malloc, hook_malloc, after=False)
    initial_state.add_hook(free, hook_free, after=False)
    
    initial_state.context['sbrk'] = sbrk
    initial_state.context['mmap'] = mmap
    initial_state.context['munmap'] = munmap


def hook_mmap_return(state: State):
    """ Hook to process munmap information and add a function hook to the callsite of munmap (which should 
    be inside malloc or another function inside of malloc which calls munmap), post execution of the
    munmap call.
    """
    ret_val = state.cpu.read_register("RAX")
    logger.info(f"mmap ret val: {hex(ret_val)}")

    state.context["malloc_lib"].process_mmap(ret_val, state.context["mmap_args"])
    del state.context["mmap_args"]

    logger.debug(f"Unhooking mmap return in malloc in state: {state.id}")
    state.remove_hook(state.cpu.read_register("RIP"), hook_mmap_return)


def hook_mmap(state: State):
    """ Hook to process mmap information and add a function hook to the callsite of mmap (which should 
    be inside the free or another function inside of free which calls mmap), post execution of the
    mmap call.
    """
    # TODO(Sonya): per Eric's suggestion -
    #  check out manticore invoke model code to find function that will extract all these args
    args = []
    args.append(state.cpu.read_register("RDI"))  # void *addr
    args.append(state.cpu.read_register("RSI"))  # size_t length
    args.append(state.cpu.read_register("RDX"))  # int prot
    args.append(state.cpu.read_register("RCX"))  # int flags
    args.append(state.cpu.read_register("R8"))  # int fd
    args.append(state.cpu.read_register("R9"))  # off_t offset
    logger.info(f"Invoking mmap in malloc. Args {args}")
    state.context["mmap_args"] = args

    ret_addr = load_ret_addr("mmap", state)
    state.add_hook(ret_addr, hook_mmap_return, after=False)

# NOTE(Sonya): If I can't find the internal sbrk address I can get to manticore brk.
# .....so I can calculate: sbrk_chunk size = curr_brk - new_brk, sbrk_ret_val = new_brk
# where new_brk is the argument passed into brk - see brk and sbrk man pages
# https://github.com/trailofbits/manticore/blob/f46f78b69bd440af144f19ec97695ec7e911a374/manticore/platforms/linux.py#L1864
# state.platform.brk gives current brk
def hook_sbrk_return(state: State):
    """ Hook to process sbrk return information and remove the hook to itself at the callsite to sbrk,
    post execution of the sbrk function.
    """
    ret_val = state.cpu.read_register("RAX")
    logger.info(f"sbrk ret val: {hex(ret_val)}")

    state.context["malloc_lib"].process_sbrk(ret_val, state.context["sbrk_size"])
    del state.context["sbrk_size"]

    logger.debug(f"Unhooking sbrk return in malloc in state: {state.id}")
    state.remove_hook(state.cpu.read_register("RIP"), hook_sbrk_return)


def hook_sbrk(state: State):
    """ Hook to process sbrk information and add a function hook to the callsite of sbrk (which should 
    be inside malloc or another function inside of malloc which calls sbrk), post execution of the
    sbrk call.
    """
    # Get %rdi is first arg reg get request size from it
    request_size = state.cpu.read_register("RDI")
    logger.info(f"Invoking sbrk in malloc. Request Size {request_size}")
    state.context["sbrk_size"] = request_size

    # Pull return address off the stack and add a hook for it
    ret_addr = load_ret_addr("sbrk", state)
    state.add_hook(ret_addr, hook_sbrk_return, after=False)


def hook_malloc_return(state: State):
    """ Hook to process malloc information and remove function hooks at the return address, 
    post execution of the malloc function.
    """
    ret_val = state.cpu.read_register("RAX")
    logger.info(f"malloc ret val: {hex(ret_val)}")
    state.context["malloc_lib"].process_malloc(ret_val, state.context["malloc_size"])
    del state.context["malloc_size"]

    if HOOK_SBRK_INFO:
        logger.debug((f"Unhooking sbrk in state: {state.id}"))
        state.remove_hook(state.context["sbrk"], hook_sbrk)

    if HOOK_MMAP_INFO:
        logger.debug(f"Unhooking mmap in state: {state.id}")
        state.remove_hook(state.context["mmap"], hook_mmap)

    logger.debug(f"Unhooking malloc return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("RIP"), hook_malloc_return)

    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_malloc(state: State):
    """ Hook to process malloc information and add function hooks at malloc function start, 
    pre-execution of the malloc function.
    """
    # Get request size
    malloc_size = state.cpu.read_register("RDI")
    logger.info(f"Invoking malloc for size: {malloc_size}")
    state.context["malloc_size"] = malloc_size

    # Hook sbrk
    if HOOK_SBRK_INFO:
        logger.debug(f"Adding Hook for sbrk in state: {state.id}")
        state.add_hook(state.context['sbrk'], hook_sbrk, after=False)

    # Hook mmap
    if HOOK_MMAP_INFO:
        logger.debug(f"Adding Hook for mmap in state: {state.id}")
        state.add_hook(state.context["mmap"], hook_mmap, after=False)

    # Hook Return Address
    if HOOK_MALLOC_RETURN:
        ret_addr = load_ret_addr("malloc", state)
        state.add_hook(ret_addr, hook_malloc_return, after=False)


def hook_munmap_return(state: State):
    """ Hook to process munmap information and add a function hook to the callsite of munmap (which should 
    be inside malloc or another function inside of malloc which calls munmap), post execution of the
    munmap call.
    """
    ret_val = state.cpu.read_register("RAX")
    logger.info(f"munmap ret val: {hex(ret_val)}")

    logger.debug(f"Unhooking munmap return in malloc in state: {state.id}")
    state.remove_hook(state.cpu.read_register("RIP"), hook_munmap_return)


def hook_munmap(state: State):
    """ Hook to process munmap information and add a function hook to the callsite of munmap (which should 
    be inside the free or another function inside of free which calls munmap), post execution of the
    munmap call.
    """
    addr = state.cpu.read_register("RDI")  # void *addr
    length = state.cpu.read_register("RSI")  # size_t length
    logger.info(f"Invoking munmap in malloc. Args {addr}, {length}")

    state.context["malloc_lib"].process_munmap(addr, length)

    ret_addr = load_ret_addr("munmap", state)
    state.add_hook(ret_addr, hook_munmap_return, after=False)


def hook_free_return(state: State):
    """ Hook to process free information and remove function hooks at the callsite, 
    post execution of the free function.
    """
    logger.info(f"Free has no return value")

    if HOOK_MMAP_INFO:
        logger.debug(f"Unhooking munmap in state: {state.id}")
        state.remove_hook(state.context['munmap'], hook_munmap)

    logger.debug(f"Unhooking free return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("RIP"), hook_free_return)

    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_free(state: State):
    """ Hook to process free information and add function hooks at free function start,
    pre-execution of the free function.
    """
    # Get free address
    free_address = state.cpu.read_register("RDI")
    logger.info(f"Attempting to free: {hex(free_address)}")
    state.context["malloc_lib"].process_free(free_address)

    # Hook munmap
    if HOOK_MMAP_INFO:
        logger.debug(f"Adding Hook for munmap in state: {state.id}")
        state.add_hook(state.context['munmap'], hook_munmap, after=False)

    # Hook free return address
    if HOOK_FREE_RETURN:
        ret_addr = load_ret_addr("free", state)
        state.add_hook(ret_addr, hook_free_return, after=False)
