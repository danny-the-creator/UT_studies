/*  Smash.c - Demonstrate how to overwrite the stack, causing the stack
    frame to be damaged. Compile with stack protection enabled to prevent
    the problem.  */

#include <stdio.h>
#include <string.h>

void smash(const char *fr) {
    char to[2];
    strcpy(to, fr);
}

int main(int argc, char * argv[]) {
    char fr[] = "abcdefghijklmnopqrstuvwxyz";
    char to[2] ;
    strcpy(to,fr) ;
    printf("to=%p=%s\nfr=%p=%s\n", (void*)to, to, (void*)fr, fr);
    fflush(stdout);
    smash(to);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
