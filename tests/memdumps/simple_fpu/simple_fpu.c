// compile with
// cl /arch:IA32 /Fe:simple_fpu.exe simple_fpu.c
//
// make memory dump with:
// .dump /ma simple_fpu.dmp

#include <stdio.h>

int main(int argc, const char* argv[])
{

    float foo = 0.0f;
    char ch ='\0';
    float *bar;
    printf("reading char, float: ");
    scanf("%c %f", &ch, &foo);
    // break for windbg
    __debugbreak();
    switch(ch) {
        case 'm':
            // error;
            *((float*)0xf00dbad0) = foo;
            printf("Should crash before here\n");
            break;
        case 'c':
            printf("Selected c\n");
            break;
        case 'b':
            printf("Selected c\n");
            bar = &foo;
            *bar = 1.23f;
            printf("float is: %f\n", foo);
            *bar = *((float*)0xf00dbadb);
            break;
        default:
            printf("Unknown option\n");

    }

    return 0;

}
