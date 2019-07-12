######################################################
CC			= gcc

IFLAGS			= -Iinclude

CFLAGS			= -g -Wall
LFLAGS 			= -shared -fPIC

OPENSSL_LFLAGS		= -lcrypto -lssl
######################################################

all: test_openssl_md5 test_openssl_bnsqr test_tweetnacl_scalarmult test_monocypher_eddsa	

init:
	mkdir include/

test_openssl_md5: test_openssl_md5.c
	$(CC) $(CFLAGS) -static -o $@ $< $(OPENSSL_LFLAGS)


test_openssl_bnsqr: test_openssl_bnsqr.c
	$(CC) $(CFLAGS) -o $@ $< $(OPENSSL_LFLAGS)


test_tweetnacl_scalarmult: test_tweetnacl_scalarmult.c
	$(CC) $(CFLAGS) -static -o $@ $<

clean:
	rm -rf ../mcore_*/
	rm test_openssl_md5 test_openssl_bnsqr test_tweetnacl_scalarmult
