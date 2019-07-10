/*
[+] expanding execution with file input.jpg 
    * 10 path constraints (bound: 0)
    * 9 path constraints (thanks to constraint subsumption)
    * solving constraints [0:0]
    * solving constraints [0:1]
      Not1(CmpEQ32(Add32(8Uto32(LDle:I8(input(0))),0x1:I32),0x0:I32))
      NOT((BVPLUS(32,(0h000000@x0),0h00000001) = 0h00000000))
    * new_input (1.jpg): ......JFIF
    * solving constraints [0:2]
      CmpEQ32(8Uto32(LDle:I8(input(0))),0x1:I32)
      ((0h000000@x0) = 0h00000001)
    * new_input (2.jpg): ......JFIF
    * solving constraints [0:3]
      CmpEQ32(8Uto32(LDle:I8(input(0))),0xff:I32)
      ((0h000000@x0) = 0h000000ff)
    ! unsolvable constraint, skipping it !
    
[+] 0x0409c263 depending of input: if (32to1(1Uto32(CmpEQ32(Add32(GET:I32(PUT(8Uto32(LDle:I8(input(0))))),0x1:I32),0x0:I32)))) => 0
[+] overwriting an address: STle(GET:I32(PUT(GET:I32(PUT(GET:I32(PUT(8Uto32(LDle:I8(input(0)))))))))) = Sub32(LDle:I32(STle(GET:I32(PUT(GET:I32(PUT(GET:I32(PUT
(8Uto32(LDle:I8(input(0))))))))))),0x1:I32)
[+] 0x040971f3 depending of input: if (32to1(1Uto32(CmpEQ32(LDle:I32(STle(GET:I32(PUT(GET:I32(PUT(GET:I32(PUT(8Uto32(LDle:I8(input(0))))))))))),0x1:I32)))) => 
1
[+] 0x080487ec depending of input: if (32to1(1Uto32(CmpEQ32(LDle:I32(STle(GET:I32(PUT(GET:I32(PUT(GET:I32(PUT(GET:I32(PUT(8Uto32(LDle:I8(input(0))))))))))))),0
xff:I32)))) => 1

*/
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>


#define ERROR(x) do { perror(x); exit(-1); } while (0);


#define ERREXIT(msg)  (fprintf(stderr, "%s\n", msg), exit(EXIT_FAILURE))
#define NEXTBYTE()    getc(fp)
#define M_SOI         0xD8


static FILE *fp;

/*int getc(FILE *x) {
    unsigned char xxxx;

    return (fread(&xxxx, 1, 1, x) != 1) ? EOF : xxxx;
}*/


/*static int first_marker (void) {
    int c1, c2;

    c1 = NEXTBYTE();
    c2 = NEXTBYTE();
    if (c1 != 0xFF || c2 != M_SOI) {
        ERREXIT("Not a JPEG file");
    }
    return c2;
}*/


int main(int argc, char *argv[]) {
    //FILE *fp;
    int c1, c2;

    if (argc != 2) {
        printf("Usage: %s <file>\n", argv[0]);
        exit(-1);
    }

    if ((fp = fopen(argv[1], "rb")) == NULL) {
        ERROR("fopen");
    }

    /*c = getc(fp);
    if (c != EOF) {
        while (c > 0) {
            c--;
        }
    }*/
    c1 = getc(fp);
    c2 = getc(fp);
    if (c1 != 'g' && c2 != 'o') {
        printf("ok\n");
    }

    return 0;
}
