#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>
void signal_handler(int sig) {
        printf("Signal %d received.\n", sig);
        exit(0);
        }

int main(int argc, char *argv[]) {
    pid_t pid=fork();
    printf("%s\n", argv[0]);
    if (pid==0) { /* child process */
        signal(SIGFPE, signal_handler); 
        pause();    /*waits for signal*/
    } else  { /* pid!=0; parent process */
        usleep(10000); /*sleep for 10ms*/
        kill(pid, SIGFPE);  /*send the signal to child*/
        waitpid(pid,0,0); /* wait for child exit */
    return 0;
    }
}