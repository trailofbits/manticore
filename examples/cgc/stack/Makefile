PROGRAM_NAME=stack
SRCS = $(wildcard *.S *.c )
LDFLAGS    = -nostdlib -lcgc -L/usr/lib -static -s
CGC_CFLAGS = -m32 -nostdlib -fno-builtin -nostdinc -nostartfiles -nodefaultlibs -Iinclude -Ilib -I/usr/include $(CFLAGS)
PATH       := /usr/i386-linux-cgc/bin:$(PATH)
LD         = ld
LLC        = llc-3.4
CLANG      = clang

COBJS       = $(SRCS:.c=.o)
OBJS        = $(COBJS:.S=.o)

#cc -c -m32 -nostdlib -fno-builtin -nostdinc -nostartfiles -nodefaultlibs -Iinclude -Ilib -I/usr/include  -o build/src/main.o src/main.c
#ld -nostdlib -lcgc -L/usr/lib -static -s -o bin/array_index_validation_01 build/src/main.o


all: $(PROGRAM_NAME)


$(PROGRAM_NAME): $(OBJS)
	$(LD) $(LDFLAGS) -o $(PROGRAM_NAME) $^

%.o: %.c
	$(CC) -c $(CGC_CFLAGS) -o $@ $<

%.o: %.S
	$(CC) -c $(CGC_CFLAGS) -o $@ $<

clean:
	-rm -rf $(PROGRAM_NAME) $(OBJS)

.PHONY: all build clean


