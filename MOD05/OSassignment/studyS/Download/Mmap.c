/*  Mmap.c - Copy the file specified as the first command line argument
    to the file of the second command line argument by mapping both files
    into memory, then to copy the source file memory to the destination
    file memory. With a 3rd command line argument present the buffer is not
    written back to demonstrate the difference between MAP_PRIVATE and
    MAP_SHARED */

#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <sys/mman.h>

#define B 64

char s[B]; /* This is declared at global level to make the initialiser of pmap_argv work */

int main(int argc, char *argv[]) {
    if(argc>=3) {
        int in = open(argv[1], O_RDONLY);
        int out = open(argv[2], O_RDWR|O_CREAT|O_TRUNC, 0666);
        int flags = (argc > 3 ? MAP_PRIVATE : MAP_SHARED ) ;
        size_t sz = lseek(in, 0, SEEK_END);
        lseek(out, sz - 1, SEEK_SET);
        write(out, "\0", 1);
        void *src = mmap(NULL, sz, PROT_READ, MAP_PRIVATE, in, 0);
        void *tgt = mmap(NULL, sz, PROT_WRITE, flags, out, 0);
        memcpy(tgt, src, sz);
        snprintf(s, B, "%d", getpid());
        pid_t pid=fork();
        if (pid==0) {
            char *pmap_argv[]={"pmap","-x",s,NULL};
            execv("/usr/bin/pmap", pmap_argv);
        }
        sleep(1);
        munmap(src, sz);
        munmap(tgt, sz);
        close(in);
        close(out);
        return 0;
    } else {
        printf("usage: %s in out [prot]\n", argv[0]);
        return 1;
    }
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
