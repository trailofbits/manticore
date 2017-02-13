#-------------------------------------------------------------------------------
# elftools: elf/constants.py
#
# Constants and flags, placed into classes for namespacing
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------

class E_FLAGS(object):
    """ Flag values for the e_flags field of the ELF header
    """
    EF_ARM_EABIMASK=0xFF000000
    EF_ARM_EABI_VER1=0x01000000
    EF_ARM_EABI_VER2=0x02000000
    EF_ARM_EABI_VER3=0x03000000
    EF_ARM_EABI_VER4=0x04000000
    EF_ARM_EABI_VER5=0x05000000
    EF_ARM_GCCMASK=0x00400FFF
    EF_ARM_HASENTRY=0x02
    EF_ARM_SYMSARESORTED=0x04
    EF_ARM_DYNSYMSUSESEGIDX=0x8
    EF_ARM_MAPSYMSFIRST=0x10
    EF_ARM_LE8=0x00400000
    EF_ARM_BE8=0x00800000
    EF_ARM_ABI_FLOAT_SOFT=0x00000200
    EF_ARM_ABI_FLOAT_HARD=0x00000400

    EF_MIPS_NOREORDER=1
    EF_MIPS_PIC=2
    EF_MIPS_CPIC=4
    EF_MIPS_XGOT=8
    EF_MIPS_64BIT_WHIRL=16
    EF_MIPS_ABI2=32
    EF_MIPS_ABI_ON32=64
    EF_MIPS_NAN2008=1024
    EF_MIPS_ARCH=0xf0000000
    EF_MIPS_ARCH_1=0x00000000
    EF_MIPS_ARCH_2=0x10000000
    EF_MIPS_ARCH_3=0x20000000
    EF_MIPS_ARCH_4=0x30000000
    EF_MIPS_ARCH_5=0x40000000
    EF_MIPS_ARCH_32=0x50000000
    EF_MIPS_ARCH_64=0x60000000
    EF_MIPS_ARCH_32R2=0x70000000
    EF_MIPS_ARCH_64R2=0x80000000

class SHN_INDICES(object):
    """ Special section indices
    """
    SHN_UNDEF=0
    SHN_LORESERVE=0xff00
    SHN_LOPROC=0xff00
    SHN_HIPROC=0xff1f
    SHN_ABS=0xfff1
    SHN_COMMON=0xfff2
    SHN_HIRESERVE=0xffff


class SH_FLAGS(object):
    """ Flag values for the sh_flags field of section headers
    """
    SHF_WRITE=0x1
    SHF_ALLOC=0x2
    SHF_EXECINSTR=0x4
    SHF_MERGE=0x10
    SHF_STRINGS=0x20
    SHF_INFO_LINK=0x40
    SHF_LINK_ORDER=0x80
    SHF_OS_NONCONFORMING=0x100
    SHF_GROUP=0x200
    SHF_TLS=0x400
    SHF_MASKOS=0x0ff00000
    SHF_EXCLUDE=0x80000000
    SHF_MASKPROC=0xf0000000


class P_FLAGS(object):
    """ Flag values for the p_flags field of program headers
    """
    PF_X=0x1
    PF_W=0x2
    PF_R=0x4
    PF_MASKOS=0x00FF0000
    PF_MASKPROC=0xFF000000


# symbol info flags for entries
# in the .SUNW_syminfo section
class SUNW_SYMINFO_FLAGS(object):
    """ Flags for the si_flags field of entries
        in the .SUNW_syminfo section
    """
    SYMINFO_FLG_DIRECT=0x1
    SYMINFO_FLG_FILTER=0x2
    SYMINFO_FLG_COPY=0x4
    SYMINFO_FLG_LAZYLOAD=0x8
    SYMINFO_FLG_DIRECTBIND=0x10
    SYMINFO_FLG_NOEXTDIRECT=0x20
    SYMINFO_FLG_AUXILIARY=0x40
    SYMINFO_FLG_INTERPOSE=0x80
    SYMINFO_FLG_CAP=0x100
    SYMINFO_FLG_DEFERRED=0x200

class VER_FLAGS(object):
    VER_FLG_BASE=0x1
    VER_FLG_WEAK=0x2
    VER_FLG_INFO=0x4 
