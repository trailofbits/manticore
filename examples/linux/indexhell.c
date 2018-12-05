/* This programs reads a M bytes from stdin, scrambles them, and sums them all. 
 * Only some buffers make the program print "You won!".
 * Increasing the number of symbolic bytes can generate path constraints too hard to solve.
 *
 * Compile with :
 *   $ gcc -static -Os indexhell.c -o indexhell
 *
 * Analyze it with:
 *   $ manticore indexhell
 *
 *   - By default, Manticore will consider all input of stdin to be symbolic
 *
 * 2017-04-24 12:46:46,227: [15880] MAIN:INFO: Loading program: ['indexhell']
 * 2017-04-24 12:46:46,228: [15880] MAIN:INFO: Workspace: ./mcore_72BTxZ
 * 2017-04-24 12:46:53,302: [15934][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f0ad114c4d0>
 * 2017-04-24 12:46:54,093: [15934][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f0ad177acd0>
 * 2017-04-24 12:46:54,944: [15934][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f0ad1051110>
 * 2017-04-24 12:46:55,907: [15934][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f0ad115f9d0>
 * 2017-04-24 12:46:56,678: [15934][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f0ad1009150>
 * 2017-04-24 12:46:57,497: [15934][0] MEMORY:INFO: Reading 1 bytes from symbolic address <manticore.core.smtlib.expression.BitVecAnd object at 0x7f0ad1016550>
 * 2017-04-24 12:47:06,520: [15934][3] EXECUTOR:INFO: Generating testcase No. 1 for state No.3 - Program finished correctly
 * 2017-04-24 12:47:09,693: [15934][5] EXECUTOR:INFO: Generating testcase No. 2 for state No.5 - Program finished correctly
 *
 *  Look at ./mcore_72BTxZ for results, you will find something like this:
 *   hexdump -C test_00000001.stdin
 *   00000000  23 80 26 ff 4f 56                                 |#.&.OV|
 *  
 * cat mcore_72BTxZ/test_00000001 | ./indexhell
 * You won!
*/

#include<stdio.h>
#define M 6

main(){
int i,count;
unsigned char buffer[M];
read(0, buffer, M);

for (i=0; i<M; i++)
    buffer[i] = buffer[buffer[i]%M] ^ buffer[i];

count = 0;
for (i=0; i < M; i++)
    count += buffer[i];

if (count == 0x123)
    printf("You won!");

return 0;
}
