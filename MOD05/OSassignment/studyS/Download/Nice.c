/* Nice.c - Fork P*Q processes that will run a one second loop R
   times. The P sets of Q processes all have a different priority. */

#define _GNU_SOURCE

#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <time.h>
#include "loop.h"

typedef enum { False=0, True=1 } bool ;

#define P 3
#define Q 3
#define R 7

int main(int argc, char *argv[]) {
    int p, q, r;
    pid_t parent = getpid() ;
    pid_t child[P][Q] ;
    bool Switch = (argc > 1); 
    cpu_set_t cpuset;

    CPU_ZERO(&cpuset);
    CPU_SET(1, &cpuset);
    sched_setaffinity(parent, sizeof(cpu_set_t), &cpuset);
    p = clock(); loop( 100 ); q=clock();

    printf("cpu=%d parent=%d policy=%d loop=%d us\n",
        sched_getcpu(), parent, sched_getscheduler(parent), (q-p) );
    fflush(stdout);

    for( p = 0; p < P; p++ ) {
        for( q = 0; q < Q; q++ ) {
            child[p][q] = fork();
            if (child[p][q] == 0) {
                child[p][q] = getpid();
                if( Switch ) {
                    setpriority(PRIO_PROCESS, child[p][q], P-1-p) ;
                } else {
                    setpriority(PRIO_PROCESS, child[p][q], p) ;
                }
                printf("cpu=%d child=%d prio=%d started.\n", sched_getcpu(),
                    child[p][q], getpriority(PRIO_PROCESS, child[p][q]) );
                fflush(stdout);
                for(r = 0; r < R; r++) {
                    loop( 100 );
		    printf("cpu=%d child=%d r=%d.\n", sched_getcpu(), child[p][q], r );
                    fflush(stdout);
                }
		printf("cpu=%d child=%d finished.\n", sched_getcpu(), child[p][q] );
                fflush(stdout);
                exit(0) ;
            }
        }
    }
    for( p = 0; p <= P; p++ ) {
        for( q = 0; q < Q; q++ ) {
            waitpid(child[p][q],0,0);
        }
    }
    printf("cpu=%d parent=%d finished.\n", sched_getcpu(), parent);
    fflush(stdout);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
