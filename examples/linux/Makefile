CC=gcc
CFLAGS=-O3 -static
NOSTDLIBFLAGS=-fno-builtin -static -nostdlib -fomit-frame-pointer -fno-stack-protector
PYTHON=python3

EXAMPLES=        \
  arguments      \
  crackme        \
  fclose         \
  fileio         \
  helloworld     \
  ibranch        \
  indexhell      \
  ioctl_bogus    \
  ioctl_socket   \
  sendmail       \
  simpleassert   \
  simple_copy    \
  sindex         \
  strncmp        \

# basic is temporarily disabled due to compatibility issues with modern toolchains
# See: https://github.com/trailofbits/manticore/issues/2679
DISABLED_EXAMPLES = basic

OTHER_EXAMPLES=nostdlib

all: $(EXAMPLES) $(OTHER_EXAMPLES)

arm: CC=arm-linux-gnueabi-gcc
arm: $(EXAMPLES)

.PHONY: list clean
list:
	@echo $(EXAMPLES)

clean:
	rm -rf $(EXAMPLES) $(OTHER_EXAMPLES) crackme.c

% : %.c
	$(CC) $(CFLAGS) $< -o $@

# basic is disabled due to compatibility issues
basic: basic.c
	@echo "WARNING: 'basic' example has compatibility issues with Manticore"
	@echo "See: https://github.com/trailofbits/manticore/issues/2679"
	@echo "Building anyway for manual testing..."
	$(CC) -O0 -fno-stack-protector -fno-pie -no-pie $< -o $@

nostdlib: nostdlib.c
	$(CC) -m32 $(NOSTDLIBFLAGS) $< -o $@

# simpleassert needs -O0
simpleassert: simpleassert.c
	$(CC) $(CFLAGS) -O0 $< -o $@

# crackme needs to be generated
crackme.c: crackme.py
	$(PYTHON) crackme.py > $@

crackme: crackme.c
	$(CC) $(CFLAGS) -O0 $< -o $@
