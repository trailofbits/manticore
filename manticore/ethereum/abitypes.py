# Minimal ethereum type signature parser.
# This parses the signature and types used to calculate the function hash
import warnings
from ..exceptions import EthereumError
import ply.yacc as yacc

# Lexer
# ------------------------------------------------------------
import ply.lex as lex
import re

# List of token names.   This is always required
tokens = (
    "COMMA",
    "LPAREN",
    "RPAREN",
    "LBRAKET",
    "RBRAKET",
    "NUMBER",
    "UINTN",
    "INTN",
    "UINT",
    "INT",
    "BOOL",
    "FIXEDMN",
    "UFIXEDMN",
    "ADDRESS",
    "FIXED",
    "UFIXED",
    "FUNCTION",
    "BYTESM",
    "BYTES",
    "STRING",
)

# Regular expression rules for simple tokens
t_LPAREN = r"\("
t_RPAREN = r"\)"
t_LBRAKET = r"\["
t_RBRAKET = r"\]"
t_COMMA = r"\,"


def t_NUMBER(t):
    r"\d+"
    t.value = int(t.value)
    return t


# A regular expression rule with some action code
def t_UINTN(t):
    r"uint(?P<size>256|248|240|232|224|216|208|200|192|184|176|168|160|152|144|136|128|120|112|104|96|88|80|72|64|56|48|40|32|24|16|8)"
    size = int(t.lexer.lexmatch.group("size"))
    t.value = ("uint", size)
    return t


def t_ADDRESS(t):
    r"address"
    t.value = ("uint", 160)
    return t


def t_BOOL(t):
    r"bool"
    t.value = ("uint", 8)
    return t


def t_UINT(t):
    r"uint"
    t.value = ("uint", 256)
    return t


def t_INTN(t):
    r"int(?P<size>256|248|240|232|224|216|208|200|192|184|176|168|160|152|144|136|128|120|112|104|96|88|80|72|64|56|48|40|32|24|16|8)"
    size = int(t.lexer.lexmatch.group("size"))
    t.value = ("int", size)
    return t


def t_INT(t):
    r"int"
    t.value = ("int", 256)
    return t


def t_FIXEDMN(t):
    r"^fixed(?P<M>256|248|240|232|224|216|208|200|192|184|176|168|160|152|144|136|128|120|112|104|96|88|80|72|64|56|48|40|32|24|16|8)x(?P<N>80|79|78|77|76|75|74|73|72|71|70|69|68|67|66|65|64|63|62|61|60|59|58|57|56|55|54|53|52|51|50|49|48|47|46|45|44|43|42|41|40|39|38|37|36|35|34|33|32|31|30|29|28|27|26|25|24|23|22|21|20|19|18|17|16|15|14|13|12|11|10|9|8|7|6|5|4|3|2|1)"
    M = int(t.lexer.lexmatch.group("M"))
    N = int(t.lexer.lexmatch.group("N"))
    t.value = ("fixed", M, N)
    return t


def t_FIXED(t):
    r"fixed"
    t.value = ("fixed", 128, 18)
    return t


def t_UFIXEDMN(t):
    r"ufixed(?P<M>256|248|240|232|224|216|208|200|192|184|176|168|160|152|144|136|128|120|112|104|96|88|80|72|64|56|48|40|32|24|16|8)x(?P<N>80|79|78|77|76|75|74|73|72|71|70|69|68|67|66|65|64|63|62|61|60|59|58|57|56|55|54|53|52|51|50|49|48|47|46|45|44|43|42|41|40|39|38|37|36|35|34|33|32|31|30|29|28|27|26|25|24|23|22|21|20|19|18|17|16|15|14|13|12|11|10|9|8|7|6|5|4|3|2|1)"
    M = int(t.lexer.lexmatch.group("M"))
    N = int(t.lexer.lexmatch.group("N"))
    t.value = ("ufixed", M, N)
    return t


def t_UFIXED(t):
    r"ufixed"
    t.value = ("ufixed", 128, 18)
    return t


def t_BYTESM(t):
    r"bytes(?P<nbytes>32|31|30|29|28|27|26|25|24|23|22|21|20|19|18|17|16|15|14|13|12|11|10|9|8|7|6|5|4|3|2|1)"
    size = int(t.lexer.lexmatch.group("nbytes"))
    t.value = ("bytesM", size)
    return t


def t_BYTES(t):
    r"bytes"
    t.value = ("bytes",)
    return t


def t_STRING(t):
    r"string"
    t.value = ("string",)
    return t


def t_FUNCTION(t):
    r"function"
    t.value = ("function",)
    return t


# Error handling rule
def t_error(t):
    raise EthereumError("Illegal character '%s'" % t.value[0])


# Build the lexer
lexer = lex.lex()


# parser
def p_basic_type(p):
    """
    T : UINTN
    T : UINT
    T : INTN
    T : INT
    T : ADDRESS
    T : BOOL
    T : FIXEDMN
    T : UFIXEDMN
    T : FIXED
    T : UFIXED
    T : BYTESM
    T : FUNCTION
    T : BYTES
    T : STRING

    """
    p[0] = p[1]


def p_type_list_one(p):
    """
    TL : T
    """
    p[0] = (p[1],)


def p_type_list(p):
    """
    TL : T COMMA TL
    """
    p[0] = (p[1],) + p[3]


def p_tuple(p):
    """
    T : LPAREN TL RPAREN
    """
    p[0] = ("tuple", p[2])


def p_tuple_empty(p):
    """
    T : LPAREN RPAREN
    """
    p[0] = ("tuple", ())


def p_dynamic_type(p):
    """
    T : T LBRAKET RBRAKET
    """
    reps = None
    base_type = p[1]
    p[0] = ("array", reps, base_type)


def p_dynamic_fixed_type(p):
    """
    T : T LBRAKET NUMBER RBRAKET
    """
    reps = int(p[3])
    base_type = p[1]
    p[0] = ("array", reps, base_type)


def p_error(p):
    raise EthereumError("Syntax Error at abitypes")
    # print(f"Syntax error at offset {lexer.lexpos:d}")


with warnings.catch_warnings():
    # yacc.yacc() doesn't close the debuglog file after generating the parser table.
    warnings.simplefilter("ignore", category=ResourceWarning)
    parser = yacc.yacc(debug=False)
parse = parser.parse


if __name__ == "__main__":
    # (((((((address,string,bytes)[1],int256)[0],bytes8[1])[],((address,string,bytes)[1],int256))[])[])[4])
    while True:
        try:
            s = input("abitype > ")  # use input() on Python 3
        except EOFError:
            break
        print("R:", parser.parse(s, debug=True, tracking=True))
