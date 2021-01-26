from typing import List, Dict, Tuple
from dataclasses import dataclass, field
import json

# Data Class to hold malloc_lib information
# - This is added to state 0 pre-manticore execution and will be saving state specific information as manticore
# forks and different program paths are found


@dataclass
class MallocLibData:
    """This class holds the malloc library data in a specific state (or on specific program path)."""

    malloc_calls: List[Tuple[int, int]] = field(default_factory=list)
    free_calls: List[int] = field(default_factory=list)
    sbrk_chunks: List[Tuple[int, int]] = field(default_factory=list)
    mmap_chunks: Dict[int, int] = field(default_factory=dict)
    munmap_chunks: Dict[int, int] = field(default_factory=dict)

    def __str__(self):
        # TODO(Sonya): This does not print address information in hexadecimal
        return (
            f"malloc calls: {self.malloc_calls}\n"
            f"free calls: {self.free_calls}\n"
            f"sbrk chunks: {self.sbrk_chunks}\n"
            f"mmap chunks: {self.mmap_chunks}\n"
        )

    def _save_to_file(self, state_id: int):
        data = {
            "malloc_calls": self.malloc_calls,
            "free_calls": self.free_calls,
            "sbrk_chunks": self.sbrk_chunks,
            "mmap_chunks": self.mmap_chunks,
        }
        with open(f"m_out/malloc_{state_id}.json", "w+") as write_file:
            json.dump(data, write_file, indent=4)

    # TODO(Sonya): Add some more methods here for helpful semantics of recording/retrieving information
    # Might want to annotate all this with instruction address information
    def process_malloc(self, ret_addr: int, size: int):
        # should add malloc call information to list
        self.malloc_calls.append((ret_addr, size))

    def process_free(self, free_addr: int):
        # Maybe remove from malloc list and add to a used_and_free list
        self.free_calls.append(free_addr)

    def process_calloc(self, nmemb: int, elem_size: int, ret_addr: int):
        # TODO(Sonya)
        pass

    def process_realloc(self, old_addr: int, new_addr: int, size: int):
        # TODO(Sonya)
        pass

    def process_sbrk(self, ret_addr: int, size: int):
        # check last chunk added to list
        # if size + address == new starting address of chunk -> add new chunk size to last allocated chunk
        # else -> add a new chunk to the list
        self.sbrk_chunks.append((ret_addr, size))

    def process_mmap(self, ret_addr: int, args: List):
        # add new chunk to the mmap_list
        self.mmap_chunks[ret_addr] = args

    def process_munmap(self, addr: int, length: int):
        # remove from mmap list and add to the munmaped list
        self.munmap_chunks[addr] = length
