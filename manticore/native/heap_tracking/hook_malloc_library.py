from manticore.native.state import State
from manticore.native import Manticore
from manticore.native.heap_tracking.malloc_lib_data import MallocLibData

import logging
from typing import Callable, Optional, Union

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)


HOOK_BRK_INFO: bool
HOOK_MMAP_INFO: bool
HOOK_MALLOC_RETURN: bool
HOOK_FREE_RETURN: bool
HOOK_CALLOC_RETURN: bool
HOOK_REALLOC_RETURN: bool

BRK_SYS_NUM: int
MMAP_SYS_NUM: int
MUNMAP_SYS_NUM: int


def read_arg(cpu, arg: Union[str, int]):
    if isinstance(arg, int):
        return cpu.read_int(arg)
    else:
        return cpu.read_register(arg)


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
        state.add_hook(MUNMAP_SYS_NUM, hook_munmap, after=False, syscall=True)


def remove_sys_freeing_hooks(state: State):
    if HOOK_MMAP_INFO:
        logger.debug(f"Unhooking munmap in state: {state.id}")
        state.remove_hook(MUNMAP_SYS_NUM, hook_munmap, syscall=True)


def add_sys_allocing_hooks(state: State):
    if HOOK_BRK_INFO:
        logger.debug(f"Adding hook for brk in state: {state.id}")
        state.add_hook(BRK_SYS_NUM, hook_brk, after=False, syscall=True)

    if HOOK_MMAP_INFO:
        logger.debug(f"Adding hook for mmap in state: {state.id}")
        state.add_hook(MMAP_SYS_NUM, hook_mmap, after=False, syscall=True)


def remove_sys_allocing_hooks(state: State):
    if HOOK_BRK_INFO:
        logger.debug(f"Unhooking brk in state: {state.id}")
        state.remove_hook(BRK_SYS_NUM, hook_brk, syscall=True)

    if HOOK_MMAP_INFO:
        logger.debug(f"Unhooking mmap in state: {state.id}")
        state.remove_hook(MMAP_SYS_NUM, hook_mmap, syscall=True)


def hook_malloc_lib(
    initial_state: State,
    malloc: int = 0x0,
    free: int = 0x0,
    calloc: int = 0x0,
    realloc: int = 0x0,
    hook_brk_info: bool = True,
    hook_mmap_info: bool = True,
    hook_malloc_ret_info: bool = True,
    hook_free_ret_info: bool = True,
    hook_calloc_ret_info: bool = True,
    hook_realloc_ret_info: bool = True,
    workspace: Optional[str] = None,
):
    """Function to add malloc hooks and do prep work
    - TODO(Sonya): would like this to eventially be __init__() method for a class
    once manticore hook callbacks have been debugged.
    (from Eric) See: https://github.com/trailofbits/manticore/blob/master/tests/native/test_state.py#L163-L218
    & https://github.com/trailofbits/manticore/blob/master/tests/native/test_state.py#L274-L278 to work on debugging this
    """
    # This features use on platforms besides amd64 is entirely untested
    assert initial_state.platform.current.machine == "amd64", (
        "This feature's use on platforms besides amd64 is " "entirely untested."
    )

    initial_state.context["malloc_lib"] = MallocLibData(workspace)

    global HOOK_BRK_INFO, HOOK_MMAP_INFO, HOOK_MALLOC_RETURN, HOOK_FREE_RETURN, HOOK_CALLOC_RETURN, HOOK_REALLOC_RETURN
    HOOK_BRK_INFO = hook_brk_info
    HOOK_MMAP_INFO = hook_mmap_info
    HOOK_MALLOC_RETURN = hook_malloc_ret_info
    HOOK_FREE_RETURN = hook_free_ret_info
    HOOK_CALLOC_RETURN = hook_calloc_ret_info
    HOOK_REALLOC_RETURN = hook_realloc_ret_info

    # Add requested malloc lib hooks
    if malloc:
        initial_state.add_hook(malloc, hook_malloc, after=False)
    if free:
        initial_state.add_hook(free, hook_free, after=False)
    if calloc:
        initial_state.add_hook(calloc, hook_calloc, after=False)
    if realloc:
        initial_state.add_hook(realloc, hook_realloc, after=False)

    # Import syscall numbers for current architecture
    global BRK_SYS_NUM, MMAP_SYS_NUM, MUNMAP_SYS_NUM
    from . import heap_syscalls

    table = getattr(heap_syscalls, initial_state.platform.current.machine)
    BRK_SYS_NUM = table["brk"]
    MMAP_SYS_NUM = table["mmap"]
    MUNMAP_SYS_NUM = table["munmap"]


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

    logger.debug(f"Unhooking mmap return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_mmap_return)


def hook_mmap(state: State):
    """Hook to process mmap information and add a function hook to the callsite of mmap (which should
    be inside the free or another function inside of free which calls mmap), post execution of the
    mmap call.
    void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
    """
    args = []
    args_gen = state._platform._function_abi.get_arguments()
    args.append(read_arg(state.cpu, next(args_gen)))  # void *addr
    args.append(read_arg(state.cpu, next(args_gen)))  # size_t length
    args.append(read_arg(state.cpu, next(args_gen)))  # int prot
    args.append(read_arg(state.cpu, next(args_gen)))  # int flags
    args.append(read_arg(state.cpu, next(args_gen)))  # int fd
    args.append(read_arg(state.cpu, next(args_gen)))  # off_t offset
    logger.info(f"Invoking mmap in malloc. Args {args}")
    state.context["mmap_args"] = args

    add_ret_hook("mmap", state, hook_mmap_return)


def hook_brk_return(state: State):
    """Hook to process brk return information and remove the hook to itself at the callsite to brk,
    post execution of the brk function.
    brk() returns 0 - on error, -1 is returned
    """
    ret_val = state.cpu.read_register(state._platform._function_abi.get_return_reg())
    logger.info(f"brk ret val: {hex(ret_val)}")

    state.context["malloc_lib"].process_brk(ret_val, state.context["brk_increment"])
    del state.context["brk_increment"]

    logger.debug(f"Unhooking brk return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_brk_return)


def hook_brk(state: State):
    """Hook to process brk information and add a function hook to the callsite of brk (which should
    be inside malloc or another function inside of malloc which calls brk), post execution of the
    brk call.
    Note (Sonya): Reminder that any call to sbrk with a val of 0 will never reach brk
    Note (Sonya): See https://code.woboq.org/userspace/glibc/misc/sbrk.c.html for approximate
                sbrk implementation
    void *sbrk(intptr_t increment);
    int brk(void *addr);
    """
    # Get request size from arg1
    addr = read_arg(state.cpu, next(state._platform._function_abi.get_arguments()))
    increment = addr - state.platform.brk
    logger.info(
        f"Invoking brk. Request address: {addr} for an increment of {increment}. Old brk: {state.platform.brk}"
    )
    state.context["brk_increment"] = increment

    # Pull return address off the stack and add a hook for it
    add_ret_hook("brk", state, hook_brk_return)


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
    malloc_size = read_arg(state.cpu, next(state._platform._function_abi.get_arguments()))
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

    logger.debug(f"Unhooking munmap return in state: {state.id}")
    state.remove_hook(state.cpu.read_register("PC"), hook_munmap_return)


def hook_munmap(state: State):
    """Hook to process munmap information and add a function hook to the callsite of munmap (which should
    be inside the free or another function inside of free which calls munmap), post execution of the
    munmap call.
    int munmap(void *addr, size_t length);
    """
    args_gen = state._platform._function_abi.get_arguments()
    addr = read_arg(state.cpu, next(args_gen))  # void *addr
    length = read_arg(state.cpu, next(args_gen))  # size_t length
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
    free_address = read_arg(state.cpu, next(state._platform._function_abi.get_arguments()))
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
    state.remove_hook(state.cpu.read_register("PC"), hook_calloc_return)
    logger.debug(f"Remaining hooks in state {state.id}: {state._hooks}")


def hook_calloc(state: State):
    """Hook to process calloc information and add function hooks at calloc function start,
    pre-execution of the calloc function.
    void *calloc(size_t nmemb, size_t size);
    """
    args_gen = state._platform._function_abi.get_arguments()
    nmemb = read_arg(state.cpu, next(args_gen))
    elem_size = read_arg(state.cpu, next(args_gen))
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
    ptr = read_arg(state.cpu, next(args_gen))
    new_size = read_arg(state.cpu, next(args_gen))
    logger.info(f"Attempting to realloc: {hex(ptr)} to a requested size of {new_size}")
    state.context["realloc_request"] = (ptr, new_size)

    add_sys_allocing_hooks(state)
    add_sys_freeing_hooks(state)

    # Hook realloc return address
    if HOOK_REALLOC_RETURN:
        add_ret_hook("realloc", state, hook_realloc_return)
