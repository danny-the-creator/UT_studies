/*  Getrusage.c - Initialise a large buffer to show at which indices
    page faults occur. With a command line argument the buffer is locked
    into memory to demonstrate the difference between demand paging and
    pre paging. */

#include <stdio.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <sys/resource.h>

#define N 8
#define P 4096 /* Page size */

typedef struct { int cnt; int flt; } cntflt;
typedef enum { False=0, True=1 } bool ;

int main(int argc, char* argv[]) {
    int i,k=0;
    cntflt cf[N+1];
    char buffer[N*P];
    bool Lock = (argc > 1); /* lock the buffer in memory on/off */
    struct rusage usage;
    if( Lock ) {
        mlock( buffer, N*P ) ;
    }
    getrusage(RUSAGE_SELF, &usage);
    cf[k].cnt = 0; cf[k].flt = usage.ru_minflt;
    for (i=0; i < N*P; i++) {
        buffer[i] = 0;
        getrusage(RUSAGE_SELF, &usage);
        if( cf[k].flt != usage.ru_minflt ) {
            k++;
            cf[k].cnt = i; cf[k].flt = usage.ru_minflt;
#ifdef DIRECT
            printf("cnt=%8x, flt=%d\n", cf[k].cnt, cf[k].flt);
#endif
        }
    }
#ifndef DIRECT
    for (i=0; i <= k; i++) {
        printf("cnt=%8x, flt=%d\n", cf[i].cnt, cf[i].flt);
    }
#endif
    printf("Lock=%s\n", (Lock?"on":"off"));
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
