/* This program parses a command line argument.
 *
 * Compile with :
 *   $ gcc -static -Os arguments.c -o arguments
 *
 * Analyze it with:
 *   $ manticore arguments ++++++++++
 *
 *   - Note that the character + will be replaced by a symbolic byte
 *     representing all possible bytes (except \x00)
 *     The length of the argument is important as it wont allow \x00
 *     in the middle of the argument
 * 
 * Expected output:
 *  $ manticore  arguments +++++++++
 *  2017-04-21 17:12:01,241: [4783] MAIN:INFO: Loading program: ['arguments', '+++++++++']
 *  2017-04-21 17:12:01,242: [4783] MAIN:INFO: Workspace: ./mcore_dG3b5O
 *  2017-04-21 17:12:34,130: [4835][3] EXECUTOR:INFO: Generating testcase No. 1 for state No.3 - Program finished correctly
 *  2017-04-21 17:12:48,745: [4840][11] EXECUTOR:INFO: Generating testcase No. 2 for state No.11 - Program finished correctly
 *  2017-04-21 17:13:00,509: [4840][17] EXECUTOR:INFO: Generating testcase No. 3 for state No.17 - Program finished correctly
 *  2017-04-21 17:13:10,748: [4833][21] EXECUTOR:INFO: Generating testcase No. 4 for state No.21 - Program finished correctly
 *  2017-04-21 17:13:20,580: [4833][29] EXECUTOR:INFO: Generating testcase No. 5 for state No.29 - Program finished correctly
 *  2017-04-21 17:13:28,560: [4834][33] EXECUTOR:INFO: Generating testcase No. 6 for state No.33 - Program finished correctly
 *  2017-04-21 17:13:38,583: [4838][41] EXECUTOR:INFO: Generating testcase No. 7 for state No.41 - Program finished correctly
 *  2017-04-21 17:13:47,878: [4840][47] EXECUTOR:INFO: Generating testcase No. 8 for state No.47 - Program finished correctly
 *  2017-04-21 17:13:52,500: [4835][53] EXECUTOR:INFO: Generating testcase No. 9 for state No.53 - Program finished correctly
 *  2017-04-21 17:13:52,988: [4840][51] EXECUTOR:INFO: Generating testcase No. 10 for state No.51 - Program finished correctly
 *
 *  Look at ./mcore_dG3b5O for results, you will find something like this:
 *  command.sh                  #The original command line
 *  test_00000001.messages      #A txt file with cpu and memory state 
 *  test_00000001.smt           #The smtlib description of the path constraint leading here
 *  test_00000001.stderr        #stderr output of the program
 *  test_00000001.stdin         #stdin an example stdin input 
 *  test_00000001.stdout        #stdout output of the program
 *  test_00000001.syscalls      #The trace of IO syscalls
 *  test_00000001.trace         #The list of visited instructions
 *  test_00000001.txt           #A solution to all symbolic variables used. (Includes ARGV/ENVP)
 * 
 * $ cat t*txt |grep ARGV
 * ARGV1_1: '\x01\x01\x01\x01\x01\x01\x01\x01\x01'
 * ARGV1_1: '-\x01\x01\x01\x01\x01\x01\x01\x01'
 * ARGV1_1: '--\x01\x01\x01\x01\x01\x01\x01'
 * ARGV1_1: '--d\x01\x01\x01\x01\x01\x01'
 * ARGV1_1: '--do\x01\x01\x01\x01\x01'
 * ARGV1_1: '--dos\x01\x01\x01\x01'
 * ARGV1_1: '--dost\x01\x01\x01'
 * ARGV1_1: '--dostu\x01\x01'
 * ARGV1_1: '--dostuff'
 * ARGV1_1: '--dostuf\x01'
 *
*/

#include <stdio.h>
#include <string.h>


int main(int argc, char* argv[], char* envp[]){
    int i;
    
    printf("Got %d arguments.\n", argc);
    if(argc > 1){
        if (!strcmp(argv[1], "--dostuff")){
            printf ("Do stuff!\n");
	    return 1;
	    }
    }
        
printf ("Don't do anything!\n");
return 0;
}


