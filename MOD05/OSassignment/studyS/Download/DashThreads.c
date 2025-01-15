#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

void *dash(void *emp);
void *underscore(void *emp);

int main(int argc, char** argv)
{
    pthread_t thrdash, thrunderscore;
    setbuf(stdout, NULL);
    printf("Launching the threads dash and underscore\n");
    pthread_create(&thrdash, NULL, dash, NULL);
    pthread_create(&thrunderscore, NULL, underscore, NULL);
    pthread_join(thrdash, NULL);
    pthread_join(thrunderscore, NULL);
    printf("\nBoth threads finished\n");
    printf("End of main thread\n");
    pthread_exit(NULL);
    return EXIT_SUCCESS;
}

void *dash(void *emp)
{
    int i;
    char c1 = '-';
    for (i = 1; i <= 250; i++)
    {
        write(1, &c1, 1);
    }
    return NULL;
}

void *underscore(void *emp)
{
    int i;
    char c1 = '_';
    for (i = 1; i <= 250; i++)
    {
        write(1, &c1, 1);
    }
    return NULL;
}
