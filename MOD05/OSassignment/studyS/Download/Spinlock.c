/*  Spinlock.c - Demonstrate the compare-and-swap instruction by releasing
    a lock after 1 second. */

#include <stdio.h>
#include <unistd.h>
#include <pthread.h>

int Lock = 1;

void *tproc(void *ptr) {
    sleep(1);
    Lock = 0;
    pthread_exit(0);
}

int main(int argc, char * argv[]) {
    int i;
    pthread_t thread;
    pthread_create(&thread, NULL, &tproc, NULL);
    for(i=0; !__sync_bool_compare_and_swap(&Lock, 0, 2); i++) {
#ifdef YIELD
        sched_yield();
#endif
    }
    pthread_join(thread, NULL);
    printf("%d\n",i);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
