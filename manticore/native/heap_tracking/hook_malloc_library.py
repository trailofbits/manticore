from manticore.native.state import State
from manticore.native import Manticore
from manticore.native.heap_tracking.malloc_lib_data import MallocLibData

import logging
from typing import Callable

logger = logging.getLogger(__name__)
logger.setLevel(2)


HOOK_SBRK_INFO: bool
HOOK_MMAP_INFO: bool
HOOK_MALLOC_RETURN: bool
HOOK_FREE_RETURN: bool
HOOK_CALLOC_RETURN: bool
HOOK_REALLOC_RETURN: bool


def load_ret_addr(state: State) -> int:
    """Loads the return address of a function from the stack
    (Assuming the next instruction to be executed is the start of a function call)
    """
    stack_location = state.cpu.read_register("STACK")
    ret_addr = state.cpu.read_int(stack_location, state.cpu.address_bit_size)
    return ret_addr


def add_ret_hook(func: str, state: State, ret_hook: Callable[[State], None]) -> None:
    ret_addr = load_ret_addr(state)
    logger.debug(f"Adding a hook for {func} callsite in state: {state.id}")
    state.add_hook(ret_addr, ret_hook, after=False)


def add_sys_freeing_hooks(state: State):
    if HOOK_MMAP_INFO:
        logger.debug(f"Adding hook for munmap in state: {state.id}")
        state.add_hook(state.context["munmap"], hook_munmap, after=False)


def remove_sys_freeing_hooks(state: State):
    if HOOK_MMAP_INFO:
        logger.debug(f"Unhooking munmap in state: {state.id}")
        state.remove_hook(state.context["munmap"], hook_munmap)


def add_sys_allocing_hooks(state: State):
    if HOOK_SBRK_INFO:
        logger.debug(f"Adding hook for sbrk in state: {state.id}")
        state.add_hook(state.context["sbrk"], hook_sbrk, after=False)

    if HOOK_MMAP_INFO:
        logger.debug(f"Adding hook for mmap in state: {state.id}")
        state.add_hook(state.context["mmap"], hook_mmap, after=False)


def remove_sys_allocing_hooks(state: State):
    if HOOK_SBRK_INFO:
        logger.debug(f"Unhooking sbrk in state: {state.id}")
        state.remove_hook(state.context["sbrk"], hook_sbrk)

    if HOOK_MMAP_INFO:
        logger.debug(f"Unhooking mmap in state: {state.id}")
        state.remove_hook(state.context["mmap"], hook_mmap)


def hook_malloc_lib(
    initial_state: State,
    malloc: int,
    free: int,
    calloc: int,
    realloc: int,
    hook_sbrk_info: bool = True,
    hook_mmap_info: bool = True,
    hook_malloc_ret_info: bool = True,
    hook_free_ret_info: bool = True,
    hook_calloc_ret_info: bool = True,
    hook_realloc_ret_info: bool = True,
):
    """Function to add malloc hooks and do prep work
    - TODO(Sonya): would like this to eventially be __init__() method for a class
    once manticore hook callbacks have been debugged.
    (from Eric) See: https://github.com/trailofbits/manticore/blob/master/tests/native/test_state.py#L163-L218
    & https://github.com/trailofbits/manticore/blob/master/tests/native/test_state.py#L274-L278 to work on debugging this
    """
    initial_state.context["malloc_lib"] = MallocLibData()

    global HOOK_SBRK_INFO, HOOK_MMAP_INFO, HOOK_MALLOC_RETURN, HOOK_FREE_RETURN, HOOK_CALLOC_RETURN, HOOK_REALLOC_RETURN
    HOOK_SBRK_INFO = hook_sbrk_info
    HOOK_MMAP_INFO = hook_mmap_info
    HOOK_MALLOC_RETURN = hook_malloc_ret_info
    HOOK_FREE_RETURN = hook_free_ret_info
    HOOK_CALLOC_RETURN = hook_calloc_ret_info
    HOOK_REALLOC_RETURN = hook_realloc_ret_info

    # Hook malloc and free
    initial_state.add_hook(malloc, hook_malloc, after=False)
    initial_state.add_hook(free, hook_free, after=False)
    initial_state.add_hook(calloc, hook_calloc, after=False)
    initial_state.add_hook(realloc, hook_realloc, after=False)

    # TODO(Sonya) - Fixme: with syscall specific hooks
    initial_state.context["sbrk"] = 0x0
    initial_state.context["mmap"] = 0x0
    initial_state.context["munmap"] = 0x0


def hook_mmap_return(state: State):
    """Hook to process munmap information and add a function hook to the callsite of munmap (which should
    be inside malloc or another function inside of malloc which calls munmap), post execution of the
    munmap call.

    mmap() returns a pointer to the mapped area
    """
    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"mmap ret val: {hex(ret_val)}")

    state.context["malloc_lib"].process_mmap(ret_val, state.context["mmap_args"])
    del state.context["mmap_args"]

    logger.debug(f"Unhooking mmap return in malloc in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_mmap_return)


def hook_mmap(state: State):
    """Hook to process mmap information and add a function hook to the callsite of mmap (which should
    be inside the free or another function inside of free which calls mmap), post execution of the
    mmap call.

    void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
    """
    args = []
    args_gen = state._platform._function_abi.get_arguments()
    args.append(state.cpu.read_register(next(args_gen)))  # void *addr
    args.append(state.cpu.read_register(next(args_gen)))  # size_t length
    args.append(state.cpu.read_register(next(args_gen)))  # int prot
    args.append(state.cpu.read_register(next(args_gen)))  # int flags
    args.append(state.cpu.read_register(next(args_gen)))  # int fd
    args.append(state.cpu.read_register(next(args_gen)))  # off_t offset
    logger.info(f"Invoking mmap in malloc. Args {args}")
    state.context["mmap_args"] = args

    add_ret_hook("mmap", state, hook_mmap_return)


# NOTE(Sonya): If I can't find the internal sbrk address I can get to manticore brk.
# .....so I can calculate: sbrk_chunk size = curr_brk - new_brk, sbrk_ret_val = new_brk
# where new_brk is the argument passed into brk - see brk and sbrk man pages
# https://github.com/trailofbits/manticore/blob/f46f78b69bd440af144f19ec97695ec7e911a374/manticore/platforms/linux.py#L1864
# state.platform.brk gives current brk
def hook_sbrk_return(state: State):
    """Hook to process sbrk return information and remove the hook to itself at the callsite to sbrk,
    post execution of the sbrk function.

    sbrk() returns the previous program break - on error, (void *) -1 is returned
    """
    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"sbrk ret val: {hex(ret_val)}")

    state.context["malloc_lib"].process_sbrk(ret_val, state.context["sbrk_size"])
    del state.context["sbrk_size"]

    logger.debug(f"Unhooking sbrk return in malloc in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_sbrk_return)


def hook_sbrk(state: State):
    """Hook to process sbrk information and add a function hook to the callsite of sbrk (which should
    be inside malloc or another function inside of malloc which calls sbrk), post execution of the
    sbrk call.

    void *sbrk(intptr_t increment);
    """
    # Get request size from arg1
    request_size = state.cpu.read_register(next(state._platform._function_abi.get_arguments()))
    logger.info(f"Invoking sbrk in malloc. Request Size {request_size}")
    state.context["sbrk_size"] = request_size

    # Pull return address off the stack and add a hook for it
    add_ret_hook("sbrk", state, hook_sbrk_return)


def hook_malloc_return(state: State):
    """Hook to process malloc information and remove function hooks at the return address,
    post execution of the malloc function.

    malloc() returns a pointer to the allocated memory
    """
    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"malloc ret val: {hex(ret_val)}")
    state.context["malloc_lib"].process_malloc(ret_val, state.context["malloc_size"])
    del state.context["malloc_size"]

    remove_sys_allocing_hooks(state)

    logger.debug(f"Unhooking malloc return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_malloc_return)
    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_malloc(state: State):
    """Hook to process malloc information and add function hooks at malloc function start,
    pre-execution of the malloc function.

    void *malloc(size_t size);
    """
    # Get request size
    malloc_size = state.cpu.read_register(next(state._platform._function_abi.get_arguments()))
    logger.info(f"Invoking malloc for size: {malloc_size}")
    state.context["malloc_size"] = malloc_size

    add_sys_allocing_hooks(state)

    # Hook Return Address
    if HOOK_MALLOC_RETURN:
        add_ret_hook("malloc", state, hook_malloc_return)


def hook_munmap_return(state: State):
    """Hook to process munmap information and add a function hook to the callsite of munmap (which should
    be inside malloc or another function inside of malloc which calls munmap), post execution of the
    munmap call.

    munmap() returns 0, on failure -1
    """
    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"munmap ret val: {hex(ret_val)}")

    logger.debug(f"Unhooking munmap return in malloc in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_munmap_return)


def hook_munmap(state: State):
    """Hook to process munmap information and add a function hook to the callsite of munmap (which should
    be inside the free or another function inside of free which calls munmap), post execution of the
    munmap call.

    int munmap(void *addr, size_t length);
    """
    args_gen = state._platform._function_abi.get_arguments()
    addr = state.cpu.read_register(next(args_gen))  # void *addr
    length = state.cpu.read_register(next(args_gen))  # size_t length
    logger.info(f"Invoking munmap in malloc. Args {addr}, {length}")

    state.context["malloc_lib"].process_munmap(addr, length)

    add_ret_hook("munmap", state, hook_munmap_return)


def hook_free_return(state: State):
    """Hook to process free information and remove function hooks at the callsite,
    post execution of the free function.

    free() has no return value
    """
    logger.info(f"Free has no return value")

    remove_sys_freeing_hooks(state)
    logger.debug(f"Unhooking free return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_free_return)
    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_free(state: State):
    """Hook to process free information and add function hooks at free function start,
    pre-execution of the free function.

    void free(void *ptr);
    """
    # Get free address
    free_address = state.cpu.read_register(next(state._platform._function_abi.get_arguments()))
    logger.info(f"Attempting to free: {hex(free_address)}")
    state.context["malloc_lib"].process_free(free_address)

    add_sys_freeing_hooks(state)

    # Hook free return address
    if HOOK_FREE_RETURN:
        add_ret_hook("free", state, hook_free_return)


def hook_calloc_return(state: State):
    """Hook to process calloc information and remove function hooks at the callsite,
    post execution of the calloc function.

    calloc() returns a pointer to the allocated memory
    """

    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"calloc ret val: {hex(ret_val)}")
    state.context["malloc_lib"].process_calloc(
        state.context["calloc_request"][0], state.context["calloc_request"][1], ret_val
    )
    del state.context["calloc_request"]

    remove_sys_allocing_hooks(state)

    logger.debug(f"Unhooking calloc return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), calloc_free_return)
    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_calloc(state: State):
    """Hook to process calloc information and add function hooks at calloc function start,
    pre-execution of the calloc function.

    void *calloc(size_t nmemb, size_t size);
    """
    args_gen = state._platform._function_abi.get_arguments()
    nmemb = state.cpu.read_register(next(args_gen))
    elem_size = state.cpu.read_register(next(args_gen))
    logger.info(f"Invoking calloc for {nmemb} element(s) of size: {elem_size}")
    state.context["calloc_request"] = (nmemb, elem_size)

    add_sys_allocing_hooks(state)

    # Hook calloc return address
    if HOOK_CALLOC_RETURN:
        add_ret_hook("calloc", state, hook_calloc_return)


def hook_realloc_return(state: State):
    """Hook to process realloc information and remove function hooks at the callsite,
    post execution of the realloc function.

    realloc() returns a pointer to the newly allocated memory
    """

    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"realloc ret val: {hex(ret_val)}")
    state.context["malloc_lib"].process_realloc(
        state.context["realloc_request"][0], ret_val, state.context["realloc_request"][1]
    )
    del state.context["realloc_request"]

    remove_sys_allocing_hooks(state)
    remove_sys_freeing_hooks(state)

    logger.debug(f"Unhooking realloc return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_realloc_return)
    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_realloc(state: State):
    """Hook to process realloc information and add function hooks at realloc function start,
    pre-execution of the realloc function.

    void *realloc(void *ptr, size_t size);
    """
    args_gen = state._platform._function_abi.get_arguments()
    ptr = state.cpu.read_register(next(args_gen))
    new_size = state.cpu.read_register(next(args_gen))
    logger.info(f"Attempting to realloc: {hex(ptr)} to a requested size of {new_size}")
    state.context["realloc_request"] = (ptr, new_size)

    add_sys_allocing_hooks(state)
    add_sys_freeing_hooks(state)

    # Hook realloc return address
    if HOOK_REALLOC_RETURN:
        add_ret_hook("realloc", state, hook_realloc_return)
