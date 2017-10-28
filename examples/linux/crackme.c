
/* This program parses a commandline argument.
 *
 * Compile with :
 *   $ gcc -static -Os crackme.c -o crackme
 *
 * Analyze it with:
 *   $ manticore crackme 
 *
 *   - By default manticore will consider all input of stdin symbolic
 *     It will explore all possible paths, eventually finding the SCRT key
 * 
 * Expected output:
 *  $ manticore --proc 5 crackme
 *  2017-04-22 10:57:07,913: [11918] MAIN:INFO: Loading program: ['crackme']
 *  2017-04-22 10:57:07,918: [11918] MAIN:INFO: Workspace: ./mcore_fZKdZ8
 *  2017-04-22 10:57:56,068: [11969][23] EXECUTOR:INFO: Generating testcase No. 1 for state No.23 - Program finished correctly
 *  2017-04-22 10:57:56,461: [11975][21] EXECUTOR:INFO: Generating testcase No. 2 for state No.21 - Program finished correctly
 *  2017-04-22 10:57:56,877: [11978][31] EXECUTOR:INFO: Generating testcase No. 3 for state No.31 - Program finished correctly
 *  2017-04-22 10:57:57,053: [11971][35] EXECUTOR:INFO: Generating testcase No. 4 for state No.35 - Program finished correctly
 *  2017-04-22 10:57:57,817: [11970][42] EXECUTOR:INFO: Generating testcase No. 5 for state No.42 - Program finished correctly
 *  2017-04-22 10:58:26,874: [11975][30] EXECUTOR:INFO: Generating testcase No. 6 for state No.30 - Program finished correctly
 *  2017-04-22 10:58:27,187: [11969][44] EXECUTOR:INFO: Generating testcase No. 7 for state No.44 - Program finished correctly
 *  2017-04-22 10:58:27,571: [11971][27] EXECUTOR:INFO: Generating testcase No. 8 for state No.27 - Program finished correctly
 *  2017-04-22 10:58:28,567: [11978][53] EXECUTOR:INFO: Generating testcase No. 9 for state No.53 - Program finished correctly
 *  2017-04-22 10:58:33,148: [11970][51] EXECUTOR:INFO: Generating testcase No. 10 for state No.51 - Program finished correctly
 *
 *  Look at ./mcore_IJ2sPb for results, you will find something like this:
 *
 *  $ head -c 4 *.stdin
 *  ==> test_00000001.stdin <==
 *  �CMM
 *  ==> test_00000002.stdin <==
 *  �C��
 *  ==> test_00000003.stdin <==
 *  ��SS
 *  ==> test_00000004.stdin <==
 *  ����
 *  ==> test_00000005.stdin <==
 *  SCR
 *  ==> test_00000006.stdin <==
 *  S�TT
 *  ==> test_00000007.stdin <==
 *  SCRT
 *  ==> test_00000008.stdin <==
 *  S���
 *  ==> test_00000009.stdin <==
 *  SC�@
 *  ==> test_0000000a.stdin <==
 *  SC�8
 *  
*/
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>

int
main(int argc, char* argv[]){printf ("Please enter your password: \n");char xor(char a, char b){
    return a^b;
}
int c;
    if ( ((c = getchar(), (c <  0)) || xor(c, 'P') != ('S' ^ 'P')) ){
        if ( ((c = getchar(), (c <  0)) || xor(c, 'X') != ('H' ^ 'X')) ){
            if ( ((c = getchar(), (c <  0)) || xor(c, '1') != ('U' ^ '1')) ){
                printf("You are NOT in!\n");
            }else {
                printf("You are NOT in!\n");
            }
        }else {
            if ( ((c = getchar(), (c <  0)) || xor(c, '1') != ('U' ^ '1')) ){
                printf("You are NOT in!\n");
            }else {
                printf("You are NOT in!\n");
            }
        }
    }else {
        if ( ((c = getchar(), (c <  0)) || xor(c, 'X') != ('C' ^ 'X')) ){
            if ( ((c = getchar(), (c <  0)) || xor(c, '1') != ('L' ^ '1')) ){
                printf("You are NOT in!\n");
            }else {
                printf("You are NOT in!\n");
            }
        }else {
            if ( ((c = getchar(), (c >= 0)) && xor(c, '1') == ('R' ^ '1')) ){
                if ( ((c = getchar(), (c >= 0)) && xor(c, 'O') == ('T' ^ 'O')) ){
                    printf("You are in!\n");
                }else {
                    printf("You are NOT in!\n");
                }
            }else {
                if ( ((c = getchar(), (c >= 0)) && xor(c, 'O') == ('8' ^ 'O')) ){
                    printf("You are NOT in!\n");
                }else {
                    printf("You are NOT in!\n");
                }
            }
        }
    }
return 0;
}
