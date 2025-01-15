/*  Fadvise.c - Create a large file with the name specified as the first
    command line argument and either flush the disk cache (if a third
    command line argument is specified) or keep the blocks in the cache.
    This code is  based on http://insights.oetiker.ch/linux/fadvise/ */

#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define M 1024*256
#define N 500 /* number of buffers written */

int main(int argc, char *argv[]) {
    if(argc>=2) {
        int out = open(argv[1], O_RDWR|O_CREAT|O_TRUNC, 0666);
        int i,k;
        int buf[M]; /* One MByte */
        for(i=0;i<N;i++) {
            for(k=0;k<M;k++) {
                buf[k] = i*N+k;
            }
            write(out,buf,sizeof(buf));
        }
        if(argc>=3) {
            fdatasync(out);
            posix_fadvise(out, 0,0,POSIX_FADV_DONTNEED);
        }
        close(out);
        return 0;
    } else {
        printf("usage: %s out [flg]\n", argv[0]);
        return 1;
    }
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
