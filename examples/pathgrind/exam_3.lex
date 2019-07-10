digit [0-9]
digits {digit}+
whitespace [\t\n]
%%
"[" { printf("OPEN_BRAC\n");}
"]" { printf("CLOSE_BRAC\n");}
"+" { printf("ADDOP\n");}
"*" { printf("MULTOP\n");}
{digit} {printf("NUMBER = %s\n", yytext);}
whitespace;
