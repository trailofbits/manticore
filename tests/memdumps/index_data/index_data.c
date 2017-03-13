// compile with 
// cl /Fe:index_data.exe index_data.c
//
// make memory dump with:
// .dump /ma index_data.dmp
// 
#include <stdio.h>

const char *table[] = {
    "entry zero",
    "entry one",
    "entry two",
    "entry three"};

int main(int argc, const char *argv[]) {
    int index = 0;
    printf("reading an index: ");
    scanf("%d", &index);
    // break for windbg
    __debugbreak();
    const char *out = table[index];
    printf("output is: %s\n", out);

    return 0;
}
