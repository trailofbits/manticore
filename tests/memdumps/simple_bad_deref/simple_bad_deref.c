// compile with 
// cl /Fe:simple_bad_deref.exe simple_bad_deref.c
//
// make memory dump with:
// .dump /ma simple_bad_deref.dmp
#include <stdio.h>

int main(int argc, const char *argv[]) {
    char foo = '\0';
    printf("reading a char: ");
    scanf("%c", &foo);
    // break for windbg
    __debugbreak();
    switch(foo) {
        case 'm':
            // error;
            *((char*)0xf00dbad0) = foo;
            printf("Should crash before here\n");
            break;
        case 'c':
            printf("Selected c\n");
            break;
        default:
            printf("Unknown option\n");

    }

    return 0;
}
