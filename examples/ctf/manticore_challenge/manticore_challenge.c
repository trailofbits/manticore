
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int check_char_0(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 97;

    if(ch != 92) {
        exit(1);
    }
    return 1;
}

int check_char_1(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 107;
    ch += 67;

    if(ch != 105) {
        exit(1);
    }
    return 1;
}

int check_char_2(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch += 61;
    ch *= 2;

    if(ch != 252) {
        exit(1);
    }
    return 1;
}

int check_char_3(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 149;

    if(ch != 219) {
        exit(1);
    }
    return 1;
}

int check_char_4(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 19;
    ch *= 2;

    if(ch != 142) {
        exit(1);
    }
    return 1;
}

int check_char_5(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 5;
    ch *= 3;

    if(ch != 228) {
        exit(1);
    }
    return 1;
}

int check_char_6(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch += 71;

    if(ch != 138) {
        exit(1);
    }
    return 1;
}

int check_char_7(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 41;

    if(ch != 102) {
        exit(1);
    }
    return 1;
}

int check_char_8(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch += 41;
    ch += 53;

    if(ch != 176) {
        exit(1);
    }
    return 1;
}

int check_char_9(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 61;
    ch += 41;
    ch += 11;

    if(ch != 172) {
        exit(1);
    }
    return 1;
}

int check_char_10(char chr) {
    register uint8_t ch = (uint8_t) chr;
    ch ^= 47;
    ch += 29;
    ch += 67;

    if(ch != 114) {
        exit(1);
    }
    return 1;
}


int check(char *buf) {
    check_char_0(buf[0]);
    check_char_1(buf[1]);
    check_char_2(buf[2]);
    check_char_3(buf[3]);
    check_char_4(buf[4]);
    check_char_5(buf[5]);
    check_char_6(buf[6]);
    check_char_7(buf[7]);
    check_char_8(buf[8]);
    check_char_9(buf[9]);
    check_char_10(buf[10]);

    return 1;
}

int main() {
    char buf[12];
    puts("Enter code:\n");
    fgets(buf, 12, stdin);
    check(buf);
    puts("Success!\n");
    return 0;
}

