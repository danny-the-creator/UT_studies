/*  Sparse.c - Create a sparce file with the name specified as the first
    command line argument. */

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define M 1024*1024 /* One MByte */

int main(int argc, char *argv[]) {
    if( argc >= 3) {
        int out = open(argv[1], O_RDWR|O_CREAT|O_TRUNC, 0666);
        int n = atoi(argv[2]);
        lseek(out, n*M-1, SEEK_SET);
        write(out, "\0", 1);
        close(out);
        return 0;
    } else {
        printf("usage: %s out n\n", argv[0]);
        return 1;
    }
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
