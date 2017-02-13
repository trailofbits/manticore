#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// build via:
// Linux:
// clang -mno-sse -m32 -ggdb -Wall -O3 -o many_ifs many_ifs.c
// Windows
// cl.exe /arch:IA32 /Fe:many_ifs.exe many_ifs.c

#define __PASSWORD__ "passwordpasswordpasswordpasswordpasswordpasswordpasswordpassword"
#define __PASSWORD_SIZE__ 32
#define __BUF_SIZE__ 512

static float float_val = 1.0f;
const char *password = __PASSWORD__;
int cause_error[__PASSWORD_SIZE__];

static int do_checksum(char *start, char *end) {
    int ck = 0;
    for(; start != end; start++) {
        ck += (int)(*start);
    }
    return ck;
}

#define ITER() do { \
    cur = buffer[location++]; \
    pwcur = password[pwloc++]; \
    if(cur == pwcur) { \
        float_val += 8.0f; \
        unsigned char to_read = buffer[location++]; \
        if(location+to_read > size) { \
            return 0; \
        } \
        checksum += do_checksum(buffer+location, buffer+location+to_read); \
        location += to_read; \
    } else {\
        return 0;\
    }\
    if(location > size || pwloc > pwlen) {\
        return 0;\
    }\
}while(0);

int process_buffer(char *buffer, size_t size) {

#ifdef _WIN32
    __debugbreak();
#endif

    size_t location = 0;
    char cur;
    size_t pwlen = __PASSWORD_SIZE__;
    size_t pwloc = 0;
    char pwcur;
    int checksum = 0;

    if(size < 1 || pwlen < 1 ) {
        return -1;
    }

    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();

    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();

    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();

    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();
    ITER();

    int index = (int)(float_val)*0x1000;
    cause_error[index] = checksum;
    return checksum;
}


int main(int argc, const char *argv[]) {

    //cause_error = (int*)malloc(__PASSWORD_SIZE__ * sizeof(int));
    void *buffer =  malloc(__BUF_SIZE__);

    // this will crash it
    //strcpy((char*)buffer,
    //        "p\x01za\x01zs\x01zs\x01zw\x01zo\x01zr\x01zd\x01z"
    //        "p\x01za\x01zs\x01zs\x01zw\x01zo\x01zr\x01zd\x01z"
    //        "p\x01za\x01zs\x01zs\x01zw\x01zo\x01zr\x01zd\x01z"
    //        "p\x01za\x01zs\x01zs\x01zw\x01zo\x01zr\x01zd\x01z"
    //        );
    memset(buffer, 'Z', __BUF_SIZE__);

    int ret = process_buffer(buffer, __BUF_SIZE__);

    if(ret != 0 && ret != -1) {
        printf("success: %d\n", ret);
    } else {
        printf("fail\n");
    }

    free(buffer);
    return 0;
}
