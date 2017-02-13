
// compile with 
// cl /Fe:simple_parse.exe simple_parse.c
//
// make memory dump with:
// .dump /ma simple_parse.dmp
// 
#include <stdio.h>

typedef int(*parse)(const char *s);

const char* string_table[] = {
    "zero",
    "one",
    "two",
    "three"};

int parse_zero(const char *s) {
    printf("parse zero\n");
    char c = s[0] - '0';
    if(c > sizeof(string_table)/sizeof(string_table[0])) {
        printf("invalid value\n");
        return -1;
    }
    printf("string table: %s\n", string_table[c]);

    return 0;
}

int parse_one(const char *s) {
    printf("parse one\n");
    printf("not implemented\n");
    return 0;
}

int parse_two(const char *s) {
    printf("parse two\n");
    printf("%s", s);
    return 0;
}
int parse_three(const char *s) {
    char c = s[0];
    if((int)c > (int)(sizeof(string_table)/sizeof(string_table[0]))) {
        printf("invalid value\n");
        return -1;
    }
    const char *st = string_table[c];
    // ensure dereference
    char first_c = st[0];
    printf("parse three\nbroken string table: %c\n", first_c);

    return 0;
}

parse ptable[] = {
    parse_zero,
    parse_one,
    parse_two,
    parse_three};

int main(int argc, const char *argv[]) {
    struct foo {
        int index;
        char s[128];
    } myvar;
    printf("reading an entry: ");
    scanf("%d %s", &(myvar.index), myvar.s);
    // break for windbg
    __debugbreak();
    if(myvar.index > (sizeof(ptable)/sizeof(ptable[0]))) {
        printf("Invalid parse index\n");
    } else {
        parse parser = ptable[myvar.index];
        parser(myvar.s);
    }

    return 0;
}
