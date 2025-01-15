/*  Mount.c - Look up the file name passed as an argument and all its
    prefixes in the table of mounted file systems to identify all mount
    points covered by the path. */

#include <fcntl.h>
#include <stdio.h>
#include <mntent.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <libgen.h>

#define M 1024 /* max mount point file name size */

char *lookup(char *pth, char *mnt) {
    struct mntent m;
    struct stat s; 
    stat(pth, &s);
    dev_t d = s.st_dev; 
    ino_t i = s.st_ino; 
    FILE *f = setmntent("/proc/mounts", "r");
    while (getmntent_r(f, &m, mnt, M)) { 
        if (stat(m.mnt_dir, &s) != 0) { 
            continue; 
        } 
        if (s.st_dev == d && s.st_ino == i) { 
            return mnt ;
        } 
    } 
    endmntent(f); 
    return NULL;
} 

int main(int argc, char **argv) {
    if(argc>=2) {
        char pth[M] = "/", mnt[M], *end;
        strncat(pth,argv[1],M);
        for(;;) {
            if(lookup(pth,mnt) != NULL) {
                printf("%s mounted on %s\n",pth,mnt);
            } else {
                printf("%s not mounted\n",pth);
            }
            end = strrchr(pth,'/');
            if(end == NULL || end == pth) {
                break;
            } else {
                *end = '\0';
            }
        }
        return 0;
    } else {
        printf("usage: %s directory\n", argv[0]);
        return 1;
    }
} 

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
