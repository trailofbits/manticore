CC=gcc
CFLAGS=-O3 -static
NOSTDLIBFLAGS=-fno-builtin -static -nostdlib -fomit-frame-pointer

all: CFLAGS=-O3 -static 
all: NOSTDLIBFLAGS=-fno-builtin -static -nostdlib  -fomit-frame-pointer
all: nostdlib basic  sindex  strncmp  arguments ibranch sendmail crackme indexhell baby-re helloworld simple_copy simpleassert

arm: CC=arm-linux-gnueabi-gcc
arm: basic  sindex  strncmp  arguments ibranch sendmail crackme indexhell helloworld simple_copy simpleassert

.PHONY: list
list:
	@$(MAKE) -pRrq -f $(lastword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/^# File/,/^# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort | egrep -v -e '^[^[:alnum:]]' -e '^$@$$' -e clean | xargs


clean:
	rm -rf nostdlib  basic  sindex strncmp arguments sendmail ibranch crackme indexhell crackme.c simple_copy helloworld nostdlib32 nostdlib64

nostdlib: nostdlib.c 
	$(CC) -m32 $(NOSTDLIBFLAGS) $< -o $@

helloworld: helloworld.c
	$(CC) $(CFLAGS) $< -static -o $@

simple_copy: simple_copy.c
	$(CC) $(CFLAGS) $< -static -o $@

basic: basic.c
	$(CC) $(CFLAGS) $< -static -o $@

simpleassert: simpleassert.c
	$(CC) $(CFLAGS) -O0 $< -static -o $@

sindex: sindex.c
	$(CC) $(CFLAGS) $< -o $@

ibranch: ibranch.c
	$(CC) $(CFLAGS) $< -o $@

strncmp: strncmp.c
	$(CC) $(CFLAGS) $< -o $@

arguments: arguments.c
	$(CC) $(CFLAGS) $< -o $@

sendmail: sendmail.c
	gcc -static $< -o $@

crackme: crackme.py 
	python crackme.py  >crackme.c
	gcc -static -Os crackme.c -o $@

indexhell: indexhell.c
	gcc -static $< -o $@

baby-re: baby-re.c
	$(CC) $(CFLAGS) -o $@ $< -Wno-unused-result
