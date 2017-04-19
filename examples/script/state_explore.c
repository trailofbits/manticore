#include <stdio.h>

/**
 * Example code for the state state_control.py and introduce_symbolic_bytes.py
 * examples.
 *
 *  See scripts for more information.
 */

void
fill_from_stdin(int *value)
{
    read(0, value, sizeof *value);
}

int
main(int argc, char *argv[])
{
    int value;

    /**
     * If we don't receive any arguments, read value from stdin. If we do 
     * receive an argument, treat `value` as uninitialized.
     */
    if (argc < 2) {
        fill_from_stdin(&value);
    }

    if ((value & 0xff) != 0) {
        if (value >= 0x40) {
            write(1, "1", 1);
            if (value == 0x41) {
                write(1, "a", 1);
            } else if (value == 0x42) {
                write(1, "b", 1);
            } else if (value == 0x43) {
                write(1, "c", 1);
            } else if (value == 0x44) {
                write(1, "d", 1);
            } else {
                write(1, "e", 1);
            }
        } else {
            write(1, "2", 1);
        }
    } else if ((value & 0xff00) != 0) {
        if (value > 0x1000) {
            write(1, "3", 1);
        } else {
            write(1, "4", 1);
        }
    } else if ((value & 0xff0000) != 0) {
        if (value > 0xf0000) {
            write(1, "5", 1);
        } else {
            write(1, "6", 1);
        }
    }
    write(1, "\n", 2);

    return 0;
}
