/*  Signal.c - Demonstrate how to handle a signal. */

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>

void signal_handler(int sig) {
    printf("Signal %d received.\n", sig);
    exit(0);
}

int main(int argc, char * argv[]) {
    int *pointer=(int *) malloc(sizeof(int));
    signal(SIGFPE, signal_handler);
    printf("About to segfault:\n");

    // Perform a division by zero to trigger SIGFPE
    int x = 0;
    int result = 100 / x;
    
    *pointer=0;
    printf("Why didn't we crash?\n");
    return 1;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
