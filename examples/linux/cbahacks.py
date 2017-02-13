import random, string, random
chars = string.ascii_uppercase + string.digits

antitrace = False
password = 'CBAHACKS#2016#01'


PROGRAM = ''
PROGRAM += '''

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
'''

if antitrace:
    PROGRAM += '''

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
'''

PROGRAM += '''
int
main(int argc, char* argv[]){'''

if antitrace:
    PROGRAM += '''
    sleep(10);
    anti_ptrace();
'''


pad = ''.join(random.choice(chars) for _ in range(len(password)))

banner = '''
This computer system is for authorized use only. All activity is logged and
regularly checked by system administrators. Individuals attempting to connect
to, port-scan, deface, hack, or otherwise interfere with any services on this
system will be reported.
 _____                                    _ 
|  __ \                                  | |
| |__) |_ _ ___ _____      _____  _ __ __| |
|  ___/ _` / __/ __\ \ /\ / / _ \| '__/ _` |
| |  | (_| \__ \__ \\\\ V  V / (_) | | | (_|
|_|   \__,_|___/___/ \_/\_/ \___/|_|  \__,_|
Authorized use only!

Please enter your password: 
'''
import json

PROGRAM += '''printf ("%s");'''%json.dumps(banner).strip('"')
PROGRAM += '''char xor(char a, char b){
    return a^b;
}
'''
PROGRAM += '''int c;\n'''

def func(password, pad, flag=True):
    if len(password) == 1:
        #SUBPROGRAMTRUE = '''if ( getchar() == 0x10 )\n'''
        if flag:
            SUBPROGRAMTRUE = '''    printf("You are in!\\n");\n'''
        else:
            SUBPROGRAMTRUE = '''    printf("You are NOT in!\\n");\n'''
    else:
        SUBPROGRAMTRUE = func(password[1:], pad[1:], flag)

    if len(password) == 1:
        SUBPROGRAMFALSE = '''    printf("You are NOT in!\\n");\n'''
    else:
        SUBPROGRAMFALSE = func(''.join(random.choice(chars) for _ in range(len(password)/2)), pad[1:], False)

    config = random.choice([ (True, SUBPROGRAMTRUE, SUBPROGRAMFALSE), (False, SUBPROGRAMFALSE, SUBPROGRAMTRUE)])
    
    SUBPROGRAM = ''
    if config[0]:
        SUBPROGRAM += '''if ( ((c = getchar(), (c >= 0)) && xor(c, '%c') == ('%c' ^ '%c')) ){\n'''%(pad[0], password[0], pad[0])
    else:
        SUBPROGRAM += '''if ( ((c = getchar(), (c <  0)) || xor(c, '%c') != ('%c' ^ '%c')) ){\n'''%(pad[0], password[0], pad[0])

    SUBPROGRAM += config[1]
    SUBPROGRAM += '''}else {\n''' 
    SUBPROGRAM += config[2]
    SUBPROGRAM += '''}'''
    SUBPROGRAM = ('\n'+('    ')).join(SUBPROGRAM.split('\n'))
    return ('    ')+SUBPROGRAM+'\n'

PROGRAM += func(password, pad)
PROGRAM += '''return 0;\n}'''
print PROGRAM

