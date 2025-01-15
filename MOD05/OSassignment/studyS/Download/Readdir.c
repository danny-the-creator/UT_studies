/*  Readdir.c - Read the current working directory and output file size */
#include <dirent.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>

int main(int argc, char *argv[]) {
    if (argc >= 2) {
        DIR *dirp = opendir(argv[1]);
        if (dirp != NULL) {
            struct dirent *dp;
            struct stat fileStat;

            while ((dp = readdir(dirp))) {
                char t;
                switch (dp->d_type) {
                    case DT_BLK: t = 'b'; break;
                    case DT_CHR: t = 'c'; break;
                    case DT_DIR: t = 'd'; break;
                    case DT_FIFO: t = 'p'; break;
                    case DT_LNK: t = 'l'; break;
                    case DT_REG: t = '-'; break;
                    case DT_SOCK: t = 's'; break;
                    default: t = '?';
                }

                // Get file size using stat
                char filePath[512];
                snprintf(filePath, sizeof(filePath), "%s/%s", argv[1], dp->d_name);
                // print the result only if the stat() call is successful, avoiding errors or invalid outputs.
                if (stat(filePath, &fileStat) == 0) { 
                    printf("%8d %c %s;  Size: %ld\n", (int)dp->d_ino, t, dp->d_name,  fileStat.st_size);
                }
            }
            closedir(dirp);
        }
        return 0;
    } else {
        printf("usage: %s dir\n", argv[0]);
        return 1;
    }
    
}
/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */

