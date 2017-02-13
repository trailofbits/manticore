#-------------------------------------------------------------------------------
# elftools: elf/structs.py
#
# Encapsulation of Construct structs for parsing an ELF file, adjusted for
# correct endianness and word-size.
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from ..construct import (
    UBInt8, UBInt16, UBInt32, UBInt64,
    ULInt8, ULInt16, ULInt32, ULInt64,
    SBInt32, SLInt32, SBInt64, SLInt64,
    Struct, Array, Enum, Padding, BitStruct, BitField, Value,
    )

from .enums import *


class ELFStructs(object):
    """ Accessible attributes:

            Elf_{byte|half|word|word64|addr|offset|sword|xword|xsword}:
                Data chunks, as specified by the ELF standard, adjusted for
                correct endianness and word-size.

            Elf_Ehdr:
                ELF file header

            Elf_Phdr:
                Program header

            Elf_Shdr:
                Section header

            Elf_Sym:
                Symbol table entry

            Elf_Rel, Elf_Rela:
                Entries in relocation sections
    """
    def __init__(self, little_endian=True, elfclass=32):
        assert elfclass == 32 or elfclass == 64
        self.little_endian = little_endian
        self.elfclass = elfclass
        self._create_structs()

    def _create_structs(self):
        if self.little_endian:
            self.Elf_byte = ULInt8
            self.Elf_half = ULInt16
            self.Elf_word = ULInt32
            self.Elf_word64 = ULInt64
            self.Elf_addr = ULInt32 if self.elfclass == 32 else ULInt64
            self.Elf_offset = self.Elf_addr
            self.Elf_sword = SLInt32
            self.Elf_xword = ULInt32 if self.elfclass == 32 else ULInt64
            self.Elf_sxword = SLInt32 if self.elfclass == 32 else SLInt64
        else:
            self.Elf_byte = UBInt8
            self.Elf_half = UBInt16
            self.Elf_word = UBInt32
            self.Elf_word64 = UBInt64
            self.Elf_addr = UBInt32 if self.elfclass == 32 else UBInt64
            self.Elf_offset = self.Elf_addr
            self.Elf_sword = SBInt32
            self.Elf_xword = UBInt32 if self.elfclass == 32 else UBInt64
            self.Elf_sxword = SBInt32 if self.elfclass == 32 else SBInt64

        self._create_ehdr()
        self._create_phdr()
        self._create_shdr()
        self._create_sym()
        self._create_rel()
        self._create_dyn()
        self._create_sunw_syminfo()
        self._create_gnu_verneed()
        self._create_gnu_verdef()
        self._create_gnu_versym()
        self._create_note()

    def _create_ehdr(self):
        self.Elf_Ehdr = Struct('Elf_Ehdr',
            Struct('e_ident',
                Array(4, self.Elf_byte('EI_MAG')),
                Enum(self.Elf_byte('EI_CLASS'), **ENUM_EI_CLASS),
                Enum(self.Elf_byte('EI_DATA'), **ENUM_EI_DATA),
                Enum(self.Elf_byte('EI_VERSION'), **ENUM_E_VERSION),
                Enum(self.Elf_byte('EI_OSABI'), **ENUM_EI_OSABI),
                self.Elf_byte('EI_ABIVERSION'),
                Padding(7)
            ),
            Enum(self.Elf_half('e_type'), **ENUM_E_TYPE),
            Enum(self.Elf_half('e_machine'), **ENUM_E_MACHINE),
            Enum(self.Elf_word('e_version'), **ENUM_E_VERSION),
            self.Elf_addr('e_entry'),
            self.Elf_offset('e_phoff'),
            self.Elf_offset('e_shoff'),
            self.Elf_word('e_flags'),
            self.Elf_half('e_ehsize'),
            self.Elf_half('e_phentsize'),
            self.Elf_half('e_phnum'),
            self.Elf_half('e_shentsize'),
            self.Elf_half('e_shnum'),
            self.Elf_half('e_shstrndx'),
        )

    def _create_phdr(self):
        if self.elfclass == 32:
            self.Elf_Phdr = Struct('Elf_Phdr',
                Enum(self.Elf_word('p_type'), **ENUM_P_TYPE),
                self.Elf_offset('p_offset'),
                self.Elf_addr('p_vaddr'),
                self.Elf_addr('p_paddr'),
                self.Elf_word('p_filesz'),
                self.Elf_word('p_memsz'),
                self.Elf_word('p_flags'),
                self.Elf_word('p_align'),
            )
        else: # 64
            self.Elf_Phdr = Struct('Elf_Phdr',
                Enum(self.Elf_word('p_type'), **ENUM_P_TYPE),
                self.Elf_word('p_flags'),
                self.Elf_offset('p_offset'),
                self.Elf_addr('p_vaddr'),
                self.Elf_addr('p_paddr'),
                self.Elf_xword('p_filesz'),
                self.Elf_xword('p_memsz'),
                self.Elf_xword('p_align'),
            )

    def _create_shdr(self):
        self.Elf_Shdr = Struct('Elf_Shdr',
            self.Elf_word('sh_name'),
            Enum(self.Elf_word('sh_type'), **ENUM_SH_TYPE),
            self.Elf_xword('sh_flags'),
            self.Elf_addr('sh_addr'),
            self.Elf_offset('sh_offset'),
            self.Elf_xword('sh_size'),
            self.Elf_word('sh_link'),
            self.Elf_word('sh_info'),
            self.Elf_xword('sh_addralign'),
            self.Elf_xword('sh_entsize'),
        )

    def _create_rel(self):
        # r_info is also taken apart into r_info_sym and r_info_type.
        # This is done in Value to avoid endianity issues while parsing.
        if self.elfclass == 32:
            r_info_sym = Value('r_info_sym',
                lambda ctx: (ctx['r_info'] >> 8) & 0xFFFFFF)
            r_info_type = Value('r_info_type',
                lambda ctx: ctx['r_info'] & 0xFF)
        else: # 64
            r_info_sym = Value('r_info_sym',
                lambda ctx: (ctx['r_info'] >> 32) & 0xFFFFFFFF)
            r_info_type = Value('r_info_type',
                lambda ctx: ctx['r_info'] & 0xFFFFFFFF)

        self.Elf_Rel = Struct('Elf_Rel',
            self.Elf_addr('r_offset'),
            self.Elf_xword('r_info'),
            r_info_sym,
            r_info_type,
        )
        self.Elf_Rela = Struct('Elf_Rela',
            self.Elf_addr('r_offset'),
            self.Elf_xword('r_info'),
            r_info_sym,
            r_info_type,
            self.Elf_sxword('r_addend'),
        )

    def _create_dyn(self):
        self.Elf_Dyn = Struct('Elf_Dyn',
            Enum(self.Elf_sxword('d_tag'), **ENUM_D_TAG),
            self.Elf_xword('d_val'),
            Value('d_ptr', lambda ctx: ctx['d_val']),
        )

    def _create_sym(self):
        # st_info is hierarchical. To access the type, use
        # container['st_info']['type']
        st_info_struct = BitStruct('st_info',
            Enum(BitField('bind', 4), **ENUM_ST_INFO_BIND),
            Enum(BitField('type', 4), **ENUM_ST_INFO_TYPE))
        # st_other is hierarchical. To access the visibility,
        # use container['st_other']['visibility']
        st_other_struct = BitStruct('st_other',
            Padding(5),
            Enum(BitField('visibility', 3), **ENUM_ST_VISIBILITY))
        if self.elfclass == 32:
            self.Elf_Sym = Struct('Elf_Sym',
                self.Elf_word('st_name'),
                self.Elf_addr('st_value'),
                self.Elf_word('st_size'),
                st_info_struct,
                st_other_struct,
                Enum(self.Elf_half('st_shndx'), **ENUM_ST_SHNDX),
            )
        else:
            self.Elf_Sym = Struct('Elf_Sym',
                self.Elf_word('st_name'),
                st_info_struct,
                st_other_struct,
                Enum(self.Elf_half('st_shndx'), **ENUM_ST_SHNDX),
                self.Elf_addr('st_value'),
                self.Elf_xword('st_size'),
            )

    def _create_sunw_syminfo(self):
        self.Elf_Sunw_Syminfo = Struct('Elf_Sunw_Syminfo',
            Enum(self.Elf_half('si_boundto'), **ENUM_SUNW_SYMINFO_BOUNDTO),
            self.Elf_half('si_flags'),
        )

    def _create_gnu_verneed(self):
        # Structure of "version needed" entries is documented in
        # Oracle "Linker and Libraries Guide", Chapter 7 Object File Format
        self.Elf_Verneed = Struct('Elf_Verneed',
            self.Elf_half('vn_version'),
            self.Elf_half('vn_cnt'),
            self.Elf_word('vn_file'),
            self.Elf_word('vn_aux'),
            self.Elf_word('vn_next'),
        )
        self.Elf_Vernaux = Struct('Elf_Vernaux',
            self.Elf_word('vna_hash'),
            self.Elf_half('vna_flags'),
            self.Elf_half('vna_other'),
            self.Elf_word('vna_name'),
            self.Elf_word('vna_next'),
        )

    def _create_gnu_verdef(self):
        # Structure off "version definition" entries are documented in
        # Oracle "Linker and Libraries Guide", Chapter 7 Object File Format
        self.Elf_Verdef = Struct('Elf_Verdef',
            self.Elf_half('vd_version'),
            self.Elf_half('vd_flags'),
            self.Elf_half('vd_ndx'),
            self.Elf_half('vd_cnt'),
            self.Elf_word('vd_hash'),
            self.Elf_word('vd_aux'),
            self.Elf_word('vd_next'),
        )
        self.Elf_Verdaux = Struct('Elf_Verdaux',
            self.Elf_word('vda_name'),
            self.Elf_word('vda_next'),
        )

    def _create_gnu_versym(self):
        # Structure off "version symbol" entries are documented in
        # Oracle "Linker and Libraries Guide", Chapter 7 Object File Format
        self.Elf_Versym = Struct('Elf_Versym',
            Enum(self.Elf_half('ndx'), **ENUM_VERSYM),
        )

    def _create_note(self):
        # Structure of "PT_NOTE" section
        self.Elf_Nhdr = Struct('Elf_Nhdr',
            self.Elf_word('n_namesz'),
            self.Elf_word('n_descsz'),
            Enum(self.Elf_word('n_type'), **ENUM_NOTE_N_TYPE),
        )
        self.Elf_Nhdr_abi = Struct('Elf_Nhdr_abi',
            Enum(self.Elf_word('abi_os'), **ENUM_NOTE_ABI_TAG_OS),
            self.Elf_word('abi_major'),
            self.Elf_word('abi_minor'),
            self.Elf_word('abi_tiny'),
        )
