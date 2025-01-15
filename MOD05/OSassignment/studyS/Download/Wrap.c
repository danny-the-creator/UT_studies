/*  Wrap.c - Copy a file, wrapping each line at position 40. */

#include <stdio.h>
#include <unistd.h>

#define N 41

int main(int argc, char * argv[]) {
    if(argc >= 3) {
        FILE *from = fopen(argv[1], "r");
        FILE *to = fopen(argv[2], "w");
        char buf[N];
        while (fgets(buf,N,from) != NULL) {
            fputs(buf,to); fputc('\n',to);
        }
        fclose(from);
        fclose(to);
        return 0;
    } else {
        printf("usage %s from to\n", argv[0]);
        return 1;
    }
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
