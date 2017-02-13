#-------------------------------------------------------------------------------
# elftools: dwarf/dwarf_expr.py
#
# Decoding DWARF expressions
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
from ..common.py3compat import BytesIO, iteritems
from ..common.utils import struct_parse, bytelist2string


# DWARF expression opcodes. name -> opcode mapping
DW_OP_name2opcode = dict(
    DW_OP_addr=0x03,
    DW_OP_deref=0x06,
    DW_OP_const1u=0x08,
    DW_OP_const1s=0x09,
    DW_OP_const2u=0x0a,
    DW_OP_const2s=0x0b,
    DW_OP_const4u=0x0c,
    DW_OP_const4s=0x0d,
    DW_OP_const8u=0x0e,
    DW_OP_const8s=0x0f,
    DW_OP_constu=0x10,
    DW_OP_consts=0x11,
    DW_OP_dup=0x12,
    DW_OP_drop=0x13,
    DW_OP_over=0x14,
    DW_OP_pick=0x15,
    DW_OP_swap=0x16,
    DW_OP_rot=0x17,
    DW_OP_xderef=0x18,
    DW_OP_abs=0x19,
    DW_OP_and=0x1a,
    DW_OP_div=0x1b,
    DW_OP_minus=0x1c,
    DW_OP_mod=0x1d,
    DW_OP_mul=0x1e,
    DW_OP_neg=0x1f,
    DW_OP_not=0x20,
    DW_OP_or=0x21,
    DW_OP_plus=0x22,
    DW_OP_plus_uconst=0x23,
    DW_OP_shl=0x24,
    DW_OP_shr=0x25,
    DW_OP_shra=0x26,
    DW_OP_xor=0x27,
    DW_OP_bra=0x28,
    DW_OP_eq=0x29,
    DW_OP_ge=0x2a,
    DW_OP_gt=0x2b,
    DW_OP_le=0x2c,
    DW_OP_lt=0x2d,
    DW_OP_ne=0x2e,
    DW_OP_skip=0x2f,
    DW_OP_regx=0x90,
    DW_OP_fbreg=0x91,
    DW_OP_bregx=0x92,
    DW_OP_piece=0x93,
    DW_OP_deref_size=0x94,
    DW_OP_xderef_size=0x95,
    DW_OP_nop=0x96,
    DW_OP_push_object_address=0x97,
    DW_OP_call2=0x98,
    DW_OP_call4=0x99,
    DW_OP_call_ref=0x9a,
    DW_OP_form_tls_address=0x9b,
    DW_OP_call_frame_cfa=0x9c,
    DW_OP_bit_piece=0x9d,
)

def _generate_dynamic_values(map, prefix, index_start, index_end, value_start):
    """ Generate values in a map (dict) dynamically. Each key starts with
        a (string) prefix, followed by an index in the inclusive range
        [index_start, index_end]. The values start at value_start.
    """
    for index in range(index_start, index_end + 1):
        name = '%s%s' % (prefix, index)
        value = value_start + index - index_start
        map[name] = value

_generate_dynamic_values(DW_OP_name2opcode, 'DW_OP_lit', 0, 31, 0x30)
_generate_dynamic_values(DW_OP_name2opcode, 'DW_OP_reg', 0, 31, 0x50)
_generate_dynamic_values(DW_OP_name2opcode, 'DW_OP_breg', 0, 31, 0x70)

# opcode -> name mapping
DW_OP_opcode2name = dict((v, k) for k, v in iteritems(DW_OP_name2opcode))


class GenericExprVisitor(object):
    """ A DWARF expression is a sequence of instructions encoded in a block
        of bytes. This class decodes the sequence into discrete instructions
        with their arguments and allows generic "visiting" to process them.

        Usage: subclass this class, and override the needed methods. The
        easiest way would be to just override _after_visit, which gets passed
        each decoded instruction (with its arguments) in order. Clients of
        the visitor then just execute process_expr. The subclass can keep
        its own internal information updated in _after_visit and provide
        methods to extract it. For a good example of this usage, see the
        ExprDumper class in the descriptions module.

        A more complex usage could be to override visiting methods for
        specific instructions, by placing them into the dispatch table.
    """
    def __init__(self, structs):
        self.structs = structs
        self._init_dispatch_table()
        self.stream = None
        self._cur_opcode = None
        self._cur_opcode_name = None
        self._cur_args = []

    def process_expr(self, expr):
        """ Process (visit) a DWARF expression. expr should be a list of
            (integer) byte values.
        """
        self.stream = BytesIO(bytelist2string(expr))

        while True:
            # Get the next opcode from the stream. If nothing is left in the
            # stream, we're done.
            byte = self.stream.read(1)
            if len(byte) == 0:
                break

            # Decode the opcode and its name
            self._cur_opcode = ord(byte)
            self._cur_opcode_name = DW_OP_opcode2name.get(
                self._cur_opcode, 'OP:0x%x' % self._cur_opcode)
            # Will be filled in by visitors
            self._cur_args = [] 

            # Dispatch to a visitor function
            visitor = self._dispatch_table.get(
                    self._cur_opcode,
                    self._default_visitor)
            visitor(self._cur_opcode, self._cur_opcode_name)

            # Finally call the post-visit function
            self._after_visit(
                    self._cur_opcode, self._cur_opcode_name, self._cur_args)

    def _after_visit(self, opcode, opcode_name, args):
        pass
        
    def _default_visitor(self, opcode, opcode_name):
        pass
        
    def _visit_OP_with_no_args(self, opcode, opcode_name):
        self._cur_args = []

    def _visit_OP_addr(self, opcode, opcode_name):
        self._cur_args = [
                struct_parse(self.structs.Dwarf_target_addr(''), self.stream)]

    def _make_visitor_arg_struct(self, struct_arg):
        """ Create a visitor method for an opcode that that accepts a single
            argument, specified by a struct.
        """
        def visitor(opcode, opcode_name):
            self._cur_args = [struct_parse(struct_arg, self.stream)]
        return visitor

    def _make_visitor_arg_struct2(self, struct_arg1, struct_arg2):
        """ Create a visitor method for an opcode that that accepts two
            arguments, specified by structs.
        """
        def visitor(opcode, opcode_name):
            self._cur_args = [
                struct_parse(struct_arg1, self.stream),
                struct_parse(struct_arg2, self.stream)]
        return visitor

    def _init_dispatch_table(self):
        self._dispatch_table = {}
        def add(opcode_name, func):
            self._dispatch_table[DW_OP_name2opcode[opcode_name]] = func
            
        add('DW_OP_addr', self._visit_OP_addr)
        add('DW_OP_const1u', 
            self._make_visitor_arg_struct(self.structs.Dwarf_uint8('')))
        add('DW_OP_const1s', 
            self._make_visitor_arg_struct(self.structs.Dwarf_int8('')))
        add('DW_OP_const2u', 
            self._make_visitor_arg_struct(self.structs.Dwarf_uint16('')))
        add('DW_OP_const2s', 
            self._make_visitor_arg_struct(self.structs.Dwarf_int16('')))
        add('DW_OP_const4u', 
            self._make_visitor_arg_struct(self.structs.Dwarf_uint32('')))
        add('DW_OP_const4s', 
            self._make_visitor_arg_struct(self.structs.Dwarf_int32('')))
        add('DW_OP_const8u', 
            self._make_visitor_arg_struct2(
                self.structs.Dwarf_uint32(''),
                self.structs.Dwarf_uint32('')))
        add('DW_OP_const8s', 
            self._make_visitor_arg_struct2(
                self.structs.Dwarf_int32(''),
                self.structs.Dwarf_int32('')))
        add('DW_OP_constu',
            self._make_visitor_arg_struct(self.structs.Dwarf_uleb128('')))
        add('DW_OP_consts',
            self._make_visitor_arg_struct(self.structs.Dwarf_sleb128('')))
        add('DW_OP_pick',
            self._make_visitor_arg_struct(self.structs.Dwarf_uint8('')))
        add('DW_OP_plus_uconst',
            self._make_visitor_arg_struct(self.structs.Dwarf_uleb128('')))
        add('DW_OP_bra', 
            self._make_visitor_arg_struct(self.structs.Dwarf_int16('')))
        add('DW_OP_skip', 
            self._make_visitor_arg_struct(self.structs.Dwarf_int16('')))

        for opname in [ 'DW_OP_deref', 'DW_OP_dup', 'DW_OP_drop', 'DW_OP_over',
                        'DW_OP_swap', 'DW_OP_swap', 'DW_OP_rot', 'DW_OP_xderef',
                        'DW_OP_abs', 'DW_OP_and', 'DW_OP_div', 'DW_OP_minus',
                        'DW_OP_mod', 'DW_OP_mul', 'DW_OP_neg', 'DW_OP_not',
                        'DW_OP_plus', 'DW_OP_shl', 'DW_OP_shr', 'DW_OP_shra',
                        'DW_OP_xor', 'DW_OP_eq', 'DW_OP_ge', 'DW_OP_gt',
                        'DW_OP_le', 'DW_OP_lt', 'DW_OP_ne', 'DW_OP_nop',
                        'DW_OP_push_object_address', 'DW_OP_form_tls_address',
                        'DW_OP_call_frame_cfa']:
            add(opname, self._visit_OP_with_no_args)

        for n in range(0, 32):
            add('DW_OP_lit%s' % n, self._visit_OP_with_no_args)
            add('DW_OP_reg%s' % n, self._visit_OP_with_no_args)
            add('DW_OP_breg%s' % n, 
                self._make_visitor_arg_struct(self.structs.Dwarf_sleb128('')))

        add('DW_OP_fbreg',
            self._make_visitor_arg_struct(self.structs.Dwarf_sleb128('')))
        add('DW_OP_regx',
            self._make_visitor_arg_struct(self.structs.Dwarf_uleb128('')))
        add('DW_OP_bregx',
            self._make_visitor_arg_struct2(
                self.structs.Dwarf_uleb128(''),
                self.structs.Dwarf_sleb128('')))
        add('DW_OP_piece',
            self._make_visitor_arg_struct(self.structs.Dwarf_uleb128('')))
        add('DW_OP_bit_piece',
            self._make_visitor_arg_struct2(
                self.structs.Dwarf_uleb128(''),
                self.structs.Dwarf_uleb128('')))
        add('DW_OP_deref_size',
            self._make_visitor_arg_struct(self.structs.Dwarf_int8('')))
        add('DW_OP_xderef_size',
            self._make_visitor_arg_struct(self.structs.Dwarf_int8('')))
        add('DW_OP_call2',
            self._make_visitor_arg_struct(self.structs.Dwarf_uint16('')))
        add('DW_OP_call4',
            self._make_visitor_arg_struct(self.structs.Dwarf_uint32('')))
        add('DW_OP_call_ref',
            self._make_visitor_arg_struct(self.structs.Dwarf_offset('')))


