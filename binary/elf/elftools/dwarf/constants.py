#-------------------------------------------------------------------------------
# elftools: dwarf/constants.py
#
# Constants and flags
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------

# Inline codes
#
DW_INL_not_inlined = 0
DW_INL_inlined = 1
DW_INL_declared_not_inlined = 2
DW_INL_declared_inlined = 3


# Source languages
#
DW_LANG_C89 = 0x0001
DW_LANG_C = 0x0002
DW_LANG_Ada83 = 0x0003
DW_LANG_C_plus_plus = 0x0004
DW_LANG_Cobol74 = 0x0005
DW_LANG_Cobol85 = 0x0006
DW_LANG_Fortran77 = 0x0007
DW_LANG_Fortran90 = 0x0008
DW_LANG_Pascal83 = 0x0009
DW_LANG_Modula2 = 0x000a
DW_LANG_Java = 0x000b
DW_LANG_C99 = 0x000c
DW_LANG_Ada95 = 0x000d
DW_LANG_Fortran95 = 0x000e
DW_LANG_PLI = 0x000f
DW_LANG_ObjC = 0x0010
DW_LANG_ObjC_plus_plus = 0x0011
DW_LANG_UPC = 0x0012
DW_LANG_D = 0x0013
DW_LANG_Python = 0x0014
DW_LANG_Mips_Assembler = 0x8001
DW_LANG_Upc = 0x8765
DW_LANG_HP_Bliss = 0x8003
DW_LANG_HP_Basic91 = 0x8004
DW_LANG_HP_Pascal91 = 0x8005
DW_LANG_HP_IMacro = 0x8006
DW_LANG_HP_Assembler = 0x8007


# Encoding
#
DW_ATE_void = 0x0
DW_ATE_address = 0x1
DW_ATE_boolean = 0x2
DW_ATE_complex_float = 0x3
DW_ATE_float = 0x4
DW_ATE_signed = 0x5
DW_ATE_signed_char = 0x6
DW_ATE_unsigned = 0x7
DW_ATE_unsigned_char = 0x8
DW_ATE_imaginary_float = 0x9
DW_ATE_packed_decimal = 0xa
DW_ATE_numeric_string = 0xb
DW_ATE_edited = 0xc
DW_ATE_signed_fixed = 0xd
DW_ATE_unsigned_fixed = 0xe
DW_ATE_decimal_float = 0xf
DW_ATE_UTF = 0x10
DW_ATE_lo_user = 0x80
DW_ATE_hi_user = 0xff
DW_ATE_HP_float80 = 0x80
DW_ATE_HP_complex_float80 = 0x81
DW_ATE_HP_float128 = 0x82
DW_ATE_HP_complex_float128 = 0x83
DW_ATE_HP_floathpintel = 0x84
DW_ATE_HP_imaginary_float80 = 0x85
DW_ATE_HP_imaginary_float128 = 0x86


# Access
#
DW_ACCESS_public = 1
DW_ACCESS_protected = 2
DW_ACCESS_private = 3


# Visibility
#
DW_VIS_local = 1
DW_VIS_exported = 2
DW_VIS_qualified = 3


# Virtuality
#
DW_VIRTUALITY_none = 0
DW_VIRTUALITY_virtual = 1
DW_VIRTUALITY_pure_virtual = 2


# ID case
#
DW_ID_case_sensitive = 0
DW_ID_up_case = 1
DW_ID_down_case = 2
DW_ID_case_insensitive = 3


# Calling convention
#
DW_CC_normal = 0x1
DW_CC_program = 0x2
DW_CC_nocall = 0x3


# Ordering
#
DW_ORD_row_major = 0
DW_ORD_col_major = 1


# Line program opcodes
#
DW_LNS_copy = 0x01
DW_LNS_advance_pc = 0x02
DW_LNS_advance_line = 0x03
DW_LNS_set_file = 0x04
DW_LNS_set_column = 0x05
DW_LNS_negate_stmt = 0x06
DW_LNS_set_basic_block = 0x07
DW_LNS_const_add_pc = 0x08
DW_LNS_fixed_advance_pc = 0x09
DW_LNS_set_prologue_end = 0x0a
DW_LNS_set_epilogue_begin = 0x0b
DW_LNS_set_isa = 0x0c
DW_LNE_end_sequence = 0x01
DW_LNE_set_address = 0x02
DW_LNE_define_file = 0x03


# Call frame instructions
#
# Note that the first 3 instructions have the so-called "primary opcode"
# (as described in DWARFv3 7.23), so only their highest 2 bits take part
# in the opcode decoding. They are kept as constants with the low bits masked
# out, and the callframe module knows how to handle this.
# The other instructions use an "extended opcode" encoded just in the low 6
# bits, with the high 2 bits, so these constants are exactly as they would
# appear in an actual file.
#
DW_CFA_advance_loc = 0b01000000
DW_CFA_offset = 0b10000000
DW_CFA_restore = 0b11000000
DW_CFA_nop = 0x00
DW_CFA_set_loc = 0x01
DW_CFA_advance_loc1 = 0x02
DW_CFA_advance_loc2 = 0x03
DW_CFA_advance_loc4 = 0x04
DW_CFA_offset_extended = 0x05
DW_CFA_restore_extended = 0x06
DW_CFA_undefined = 0x07
DW_CFA_same_value = 0x08
DW_CFA_register = 0x09
DW_CFA_remember_state = 0x0a
DW_CFA_restore_state = 0x0b
DW_CFA_def_cfa = 0x0c
DW_CFA_def_cfa_register = 0x0d
DW_CFA_def_cfa_offset = 0x0e
DW_CFA_def_cfa_expression = 0x0f
DW_CFA_expression = 0x10
DW_CFA_offset_extended_sf = 0x11
DW_CFA_def_cfa_sf = 0x12
DW_CFA_def_cfa_offset_sf = 0x13
DW_CFA_val_offset = 0x14
DW_CFA_val_offset_sf = 0x15
DW_CFA_val_expression = 0x16


