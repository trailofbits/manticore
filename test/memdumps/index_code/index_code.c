// compile with 
// cl /Fe:index_code.exe index_code.c
//
// make memory dump with:
// .dump /ma index_code.dmp
// 
#include <stdio.h>

typedef int(*my_callback)(int);

int say_zero(int a) {
    printf("entry zero");
    return a;
}
int say_one(int a) {
    printf("entry one");
    return a;
}
int say_two(int a) {
    printf("entry two");
    return a;
}
int say_three(int a) {
    printf("entry three");
    return a;
}

my_callback table[] = {
    say_zero,
    say_one,
    say_two,
    say_three};

int main(int argc, const char *argv[]) {
    int index = 0;
    printf("reading an index: ");
    scanf("%d", &index);
    // break for windbg
    __debugbreak();
    if(index > (int)(sizeof(table)/sizeof(table[0]))) {
        printf("Invalid index\n");
    } else {
        my_callback out = table[index];
        out(index);
    }


    return 0;
}
