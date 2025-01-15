/* SchedXY.c - Set the scheduler class to X and the priority to Y, then enter an long loop */

#include <sys/types.h>
#include <unistd.h>
#include <sched.h>
#include <stdio.h>

#include "loop.h"

#define M 2000 /* about 20 seconds */

int main(int argc, char *argv[]) {
    pid_t pid = getpid();
    struct sched_param param;
    param.sched_priority=Y;
    if( sched_setscheduler(pid, X, &param) != 0 ) {
        printf("cannot setscheduler\n");
    } else {
        loop(M);
    };
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
