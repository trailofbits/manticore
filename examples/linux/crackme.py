# -*- coding: utf-8 -*-

import random
import string

chars = string.ascii_uppercase + string.digits

antitrace = False
password = "SCRT"


PROGRAM = """
/* This program parses a command line argument.
 *
 * Compile with :
 *   $ gcc -static -O0 crackme.c -o crackme
 *
 * Analyze it with:
 *   $ manticore crackme
 *
 *   - By default, Manticore will consider all input of stdin to be symbolic
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
 *  ==> test_00000000.stdin <==
 *  �CMM
 *  ==> test_00000001.stdin <==
 *  �C��
 *  ==> test_00000002.stdin <==
 *  ��SS
 *  ==> test_00000003.stdin <==
 *  ����
 *  ==> test_00000004.stdin <==
 *  SCR
 *  ==> test_00000005.stdin <==
 *  S�TT
 *  ==> test_00000006.stdin <==
 *  SCRT
 *  ==> test_00000007.stdin <==
 *  S���
 *  ==> test_00000008.stdin <==
 *  SC�@
 *  ==> test_00000009.stdin <==
 *  SC�8
 *
*/
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
"""

if antitrace:
    PROGRAM += """

#include <sys/ptrace.h>
#include <sys/wait.h>
char brand[] = "http://www.julioauto.com/rants/anti_ptrace.htm";
void anti_ptrace(void)
{
    pid_t child;

    if(getenv("LD_PRELOAD"))
        while(1);


    child = fork();
    if (child){
        wait(NULL);
    }else {
       if (ptrace(PTRACE_TRACEME, 0, 1, 0) == -1)
            while(1);
       exit(0);
    }

   if (ptrace(PTRACE_TRACEME, 0, 0, 0) == -1)
        while(1);

}
"""

PROGRAM += """
int
main(int argc, char* argv[]){"""

if antitrace:
    PROGRAM += """
    sleep(10);
    anti_ptrace();
"""


pad = "".join(random.choice(chars) for _ in range(len(password)))

banner = """Please enter your password:
"""
import json

PROGRAM += """printf ("%s");""" % json.dumps(banner).strip('"')
PROGRAM += """char xor(char a, char b){
    return a^b;
}
"""
PROGRAM += """int c;\n"""


def func(password, pad, flag=True):
    if len(password) == 1:
        # SUBPROGRAMTRUE = '''if ( getchar() == 0x10 )\n'''
        if flag:
            SUBPROGRAMTRUE = """    printf("You are in!\\n");\n"""
        else:
            SUBPROGRAMTRUE = """    printf("You are NOT in!\\n");\n"""
    else:
        SUBPROGRAMTRUE = func(password[1:], pad[1:], flag)

    if len(password) == 1:
        SUBPROGRAMFALSE = """    printf("You are NOT in!\\n");\n"""
    else:
        SUBPROGRAMFALSE = func(
            "".join(random.choice(chars) for _ in range(len(password) // 2)), pad[1:], False
        )

    config = random.choice(
        [(True, SUBPROGRAMTRUE, SUBPROGRAMFALSE), (False, SUBPROGRAMFALSE, SUBPROGRAMTRUE)]
    )

    SUBPROGRAM = ""
    if config[0]:
        SUBPROGRAM += (
            """if ( ((c = getchar(), (c >= 0)) && xor(c, '%c') == ('%c' ^ '%c')) ){\n"""
            % (pad[0], password[0], pad[0])
        )
    else:
        SUBPROGRAM += (
            """if ( ((c = getchar(), (c <  0)) || xor(c, '%c') != ('%c' ^ '%c')) ){\n"""
            % (pad[0], password[0], pad[0])
        )

    SUBPROGRAM += config[1]
    SUBPROGRAM += """}else {\n"""
    SUBPROGRAM += config[2]
    SUBPROGRAM += """}"""
    SUBPROGRAM = ("\n" + ("    ")).join(SUBPROGRAM.split("\n"))
    return ("    ") + SUBPROGRAM + "\n"


PROGRAM += func(password, pad)
PROGRAM += """return 0;\n}"""

print(PROGRAM)
