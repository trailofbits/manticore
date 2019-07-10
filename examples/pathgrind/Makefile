CC=gcc
CFLAGS=-Wall -g -O2 -m32
OBJ=test test2 test3 test4 test5 test6 test7 test8 test9 test10 test11 test12 test13 test14 test15 md5 example ms08_067 strcmp

all: $(OBJ)

test: test.c
	$(CC) $(CFLAGS) -o $@ $^

test2: test2.c
	$(CC) $(CFLAGS) -o $@ $^

test3: test3.c
	$(CC) $(CFLAGS) -o $@ $^
	
test4: test4.c
	$(CC) $(CFLAGS) -o $@ $^
	
test5: test5.c
	$(CC) $(CFLAGS) -o $@ $^
	
test6: test6.c
	$(CC) $(CFLAGS) -o $@ $^
	
test7: test7.c
	$(CC) $(CFLAGS) -o $@ $^
	
test8: test8.c
	$(CC) $(CFLAGS) -o $@ $^
	
test9: test9.c
	$(CC) $(CFLAGS) -o $@ $^
	
test10: test10.c
	$(CC) $(CFLAGS) -o $@ $^
	
test11: test11.c
	$(CC) $(CFLAGS) -o $@ $^
	
test12: test12.c
	$(CC) $(CFLAGS) -o $@ $^
	
test13: test13.c
	$(CC) $(CFLAGS) -o $@ $^
	
test14: test14.c
	$(CC) $(CFLAGS) -o $@ $^
	
test15: test15.c
	$(CC) $(CFLAGS) -o $@ $^
	
md5: md5.c
	$(CC) $(CFLAGS) -o $@ $^

ms08_067: ms08_067.c
	$(CC) $(CFLAGS) -o $@ $^

urlencode: urlencode.c
	$(CC) $(CFLAGS) -o $@ $^
	
example: example.c
	$(CC) -O0 -o $@ $^

strcmp: strcmp.c
	$(CC) -O0 $(CFLAGS) -o $@ $^

clean:
	rm -f *~ $(OBJ)
