CC=gcc
CFLAGS=-O3 -static

all: CFLAGS=-O3 -static 
all: NOSTDLIBFLAGS=-m32 -fno-builtin -static -nostdlib  -fomit-frame-pointer
all: nostdlib  basic  sindex  strncmp  arguments ibranch sendmail crackme indexhell baby-re helloworld

arm: CC=arm-linux-gnueabi-gcc
arm: basic  sindex  strncmp  arguments ibranch sendmail crackme indexhell helloworld simple_copy

clean:
		rm -rf nostdlib  basic  sindex strncmp arguments sendmail server ibranch crackme indexhell crackme.c simple_copy helloworld nostdlib32 nostdlib64

nostdlib: nostdlib.c
		$(CC) -m32 -fno-builtin -static -nostdlib  -fomit-frame-pointer  nostdlib.c  -o nostdlib32
		$(CC) -m32 -fno-builtin -static -nostdlib  -fomit-frame-pointer  nostdlib.c  -o nostdlib64

helloworld: helloworld.c
		$(CC) $(CFLAGS) $< -static -o $@

simple_copy: simple_copy.c
		$(CC) $(CFLAGS) simple_copy.c -static -o simple_copy
basic: basic.c
		$(CC) $(CFLAGS) basic.c -static -o basic

sindex: sindex.c
		$(CC) $(CFLAGS) sindex.c -o sindex

ibranch: ibranch.c
		$(CC) $(CFLAGS) ibranch.c -o ibranch

strncmp: strncmp.c
		$(CC) $(CFLAGS) strncmp.c -o strncmp

arguments: arguments.c
		$(CC) $(CFLAGS) arguments.c  -o arguments

sendmail: sendmail.c
		gcc -static sendmail.c -o sendmail

server: server.c
		gcc -static server.c -o server

crackme: crackme.py 
	python crackme.py  >crackme.c
	gcc -static -Os crackme.c -o crackme

indexhell: indexhell.c
	gcc -static indexhell.c -o indexhell

baby-re: baby-re.c
	$(CC) $(CFLAGS) -o $@ $< -Wno-unused-result
