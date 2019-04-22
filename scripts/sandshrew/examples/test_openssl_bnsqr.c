/* test_openssl_bnsqr.c
 *
 *	Tests:
 *		OpenSSL Bignum Squaring
 *
 *	Description:
 *		Tests invariance between sqr and self-multiplication
 *		in OpenSSL BN_sqr() implementation.
 *
 *		NOTE: OpenSSL is a hard library for sandshrew tests to
 *		scale to. SMT timeouts will most likely incur.
 */

#include <stdlib.h>
#include <string.h>
#include <openssl/bn.h>

void SANDSHREW_BN_sqr(BIGNUM *result, BIGNUM *input, BN_CTX *ctx)
{
	BN_sqr(result, input, ctx);
}


void SANDSHREW_BN_mul(BIGNUM *result, BIGNUM *input, BN_CTX *ctx)
{
	BN_mul(result, input, input, ctx);
}


int
main(int argc, char *argv[])
{
	BN_CTX *ctx = BN_CTX_new();
	BIGNUM *x = BN_new();
	BIGNUM *r1 = BN_new();
	BIGNUM *r2 = BN_new();

	BN_bin2bn(argv[1], 32, x);

	/* test for invariance between mult and sqr */
	SANDSHREW_BN_sqr(r1, x, ctx);
	SANDSHREW_BN_mul(r2, x, ctx);

	if (BN_cmp(r1, r2) != 0)
		abort();

	/* unsafe: no frees */
	return 0;
}
