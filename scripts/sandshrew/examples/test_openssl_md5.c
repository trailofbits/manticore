/* test_openssl_md5.c
 *
 *	Tests:
 *	    OpenSSL MD5
 *
 *	Description:
 *          This is a test case that utilizes concolic execution
 *          to determine an input that produces the same hash as a fixed
 *          concrete input (aka a 'Birthday Attack'), resulting in a hash
 *          collision.
 *
 *      Results:
 *          Getting a viable solution (a working concrete input OR the original plaintext)
 *          is probabilistic. Complex SMT queries during runtime remain problematic.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/md5.h>


/* create a SANDSHREW_* wrapper over OpenSSL's MD5 for concretization */
void
SANDSHREW_MD5(unsigned char * output, char * input)
{
	MD5(input, 32, output);
}


int
main(int argc, char *argv[])
{
	unsigned char in[32];

	unsigned char orig_result[16];
	unsigned char user_result[16];
	
	SANDSHREW_MD5(orig_result, "s0m3_1nput_123");
	SANDSHREW_MD5(user_result, argv[1]);

	/* if equal, we generated a hash collision! */
	if (__strcmp_ssse3(orig_result, user_result) == 0)
		abort();
	return 0;
}
