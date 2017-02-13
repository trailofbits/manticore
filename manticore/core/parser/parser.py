# Minimal INTEL assembler expression calculator
import ply.yacc as yacc
import copy,struct
from ..smtlib import Operators,Bool
#Lexer
# ------------------------------------------------------------
# calclex.py
#
# tokenizer for a simple expression evaluator for
# numbers and +,-,*,/
# ------------------------------------------------------------
import ply.lex as lex
import re
# List of token names.   This is always required
tokens = (
   'NUMBER',
   'PLUS',
   'MINUS',
   'TIMES',
   'DIVIDE',
   'AND',
   'OR',
   'NEG',
   'LPAREN',
   'RPAREN',
   'LBRAKET',
   'RBRAKET',
   'REGISTER',
   'SEGMENT',
   'COLOM',
   'PTR',
   'TYPE',
    'RSHIFT',
    'LSHIFT',

    'LOR',
    'LAND',
    'LNOT',
    'EQ',
    'LT',
    'LE',
    'GT',
    'GE',

)

# Regular expression rules for simple tokens
t_PLUS    = r'\+'
t_MINUS   = r'-'
t_TIMES   = r'\*'
t_DIVIDE  = r'/'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBRAKET  = r'\['
t_RBRAKET  = r'\]'
t_COLOM  = r':'

t_AND    = r'&'
t_OR   = r'\|'
t_NEG   = r'~'
t_LSHIFT    = r'<<'
t_RSHIFT   = r'>>'

t_LAND    = r'&&'
t_LOR   = r'\|\|'
t_LNOT   = r'!'

t_EQ   = r'=='
t_LT   = r'<'
t_LE   = r'<='
t_GT   = r'>'
t_GE   = r'>='



re_NUMBER = re.compile(r'^(0x[a-fA-F0-9]+|[a-fA-F0-9]+)$')
re_REGISTER = re.compile(r'^(EAX|EBX|ECX|EDX|ESI|EDI|ESP|EBP|RAX|RBX|RCX|RDX|RSI|RDI|RSP|RBP|ZF|CF|SF|EFLAGS)$')
re_SEGMENT = re.compile(r'^(SS|DS|ES|SS|CS)$')
re_TYPE  = re.compile(r'^(QWORD|DWORD|WORD|BYTE)$')
re_PTR  = re.compile(r'^PTR$')

# A regular expression rule with some action code
def t_TOKEN(t):
    '[a-zA-Z0-9]+'
    #print t.value,t.lexer.lexdata[t.lexer.lexpos-len(t.value):],re_TYPE.match(t.lexer.lexdata,t.lexer.lexpos-len(t.value))
    if re_TYPE.match(t.value):
        t.type='TYPE'
    elif re_PTR.match(t.value):
        t.type='PTR'
    elif re_NUMBER.match(t.value):
        if t.value.startswith('0x'):
            t.value = t.value[2:]
        t.value = int(t.value,16)
        t.type= 'NUMBER'
    elif re_REGISTER.match(t.value):
        t.type= 'REGISTER'
    elif re_SEGMENT.match(t.value):
        t.type= 'SEGMENT'
    else:
        raise Exception("Unknown:<%s>"%t.value)
    return t

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()


#parser


precedence = (
    ('left', 'PLUS', 'MINUS'),
    ('left', 'DIVIDE'),
    ('left', 'TIMES'),
    ('left', 'AND', 'OR'),
    ('right', 'NEG'),
)



def default_read_memory(address, size):
    return "READM(%08x,%d)"%(address,size)
def default_read_register(reg):
    return "REG(%s)"%(reg)
def default_get_descriptor(selector):
    return (0, 0xfffff000, 'rwx')

default_sizes_32 = { 'QWORD': 8,
          'DWORD': 4,
          'WORD': 2,
          'BYTE': 1 }

default_sizes_64 = { 'QWORD': 8,
          'DWORD': 4,
          'WORD': 2,
          'BYTE': 1 }
functions = { 'read_memory': default_read_memory,
              'read_register': default_read_register,
              'get_descriptor': default_get_descriptor,
            }
sizes = copy.copy(default_sizes_32) 

def p_expression_div(p):
    'expression : expression DIVIDE expression'
    p[0] = p[1] / p[3]

def p_expression_mul(p):
    'expression : expression TIMES expression'
    p[0] = p[1] * p[3]

def p_expression_plus(p):
    'expression : expression PLUS expression'
    p[0] = p[1] + p[3]

def p_expression_minus(p):
    'expression : expression MINUS expression'
    p[0] = p[1] - p[3]

def p_expression_and(p):
    'expression : expression AND expression'
    p[0] = p[1] & p[3]

def p_expression_or(p):
    'expression : expression OR expression'
    p[0] = p[1] | p[3]

def p_expression_neg(p):
    'expression : NEG expression '
    p[0] = ~p[1]

def p_expression_lshift(p):
    'expression : expression LSHIFT expression'
    p[0] = p[1] << p[3]

def p_expression_rshift(p):
    'expression : expression RSHIFT expression'
    p[0] = p[1] >> p[3]

def p_expression_deref(p):
    'expression : TYPE PTR LBRAKET expression RBRAKET'
    size = sizes[p[1]]
    address = p[4]
    char_list = functions['read_memory'](address, size)
    value = Operators.CONCAT(8 * len(char_list), *reversed(map(Operators.ORD, char_list)))
    p[0] = value

def p_expression_derefseg(p):
    'expression : TYPE PTR SEGMENT COLOM LBRAKET expression RBRAKET'
    size = sizes[p[1]]
    address = p[6]
    seg = functions['read_register'](p[3])
    base, limit, _ = functions['get_descriptor'](seg)
    address = base + address
    char_list = functions['read_memory'](address, size)
    value = Operators.CONCAT(8 * len(char_list), *reversed(map(Operators.ORD, char_list)))
    p[0] = value

def p_expression_term(p):
    'expression : term'
    p[0] = p[1]

def p_factor_expr(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]

def p_term_num(p):
    'term : NUMBER'
    p[0] = p[1]

def p_term_reg(p):
    'term : REGISTER'
    p[0] = functions['read_register'](p[1])

def p_expression_eq(p):
    'expression : expression EQ expression'
    p[0] = p[1] == p[3]

def p_expression_land(p):
    'expression : expression LAND expression'
    p[0] = p[1] and p[3]

def p_expression_lor(p):
    'expression : expression LOR expression'
    p[0] = p[1] or p[3]

def p_expression_lnot(p):
    'expression : LNOT expression'
    p[0] = not p[1]

def p_expression_lt(p):
    'expression : expression LT expression'
    #p[0] = p[1] < p[3]
    p[0] = Operators.ULT(p[1], p[3])

def p_expression_le(p):
    'expression : expression LE expression'
    #p[0] = p[1] <= p[3]
    p[0] = Operators.ULE(p[1], p[3])

def p_expression_gt(p):
    'expression : expression GT expression'
    #p[0] = p[1] > p[3]
    p[0] = Operators.UGT(p[1], p[3])

def p_expression_ge(p):
    'expression : expression GE expression'
    #p[0] = p[1] >= p[3]
    p[0] = Operators.UGE(p[1], p[3])


# Error rule for syntax errors
def p_error(p):
    print "Syntax error in input:",p

# Build the parser

parser = yacc.yacc(debug=0, write_tables=0)


def parse(expression,read_memory=None,read_register=None,get_descriptor=None,word_size=32):
    global functions, sizes

    if read_memory != None:
        functions['read_memory'] = read_memory
    else:
        functions['read_memory'] = default_read_memory

    if read_register != None:
        functions['read_register'] = read_register
    else:
        functions['read_register'] = default_read_register

    if get_descriptor != None:
        functions['get_descriptor'] = get_descriptor
    else:
        functions['get_descriptor'] = default_get_descriptor

    if word_size == 32:
        sizes = copy.copy(default_sizes_32) 
    elif word_size == 64:
        sizes = copy.copy(default_sizes_64) 
    else:
        raise Exception ("Not Supported")
    result = parser.parse(expression,tracking=True)
    del functions['read_memory']
    del functions['read_register']
    del functions['get_descriptor']

    return result

if __name__ == '__main__':
    while True:
       try:
           s = raw_input('calc > ')
       except EOFError:
           break
       if not s: continue
       result = parse(s)
       print result

