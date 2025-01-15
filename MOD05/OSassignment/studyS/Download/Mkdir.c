/*  Mkdir.c - Test the directory related system calls by making a chain
    of directories Foo, Foo/Foo, Foo/Foo/Foo...  until the depth specified
    by the command line argument is reached. Create a symbolic link to
    each of the Foo* directories in the current directory. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define M 1024 /* Maximum size of directory name */
#define Dir "Foo"

int main(int argc, char* argv[]) {
    int i;
    int n = (argc==1?1:atoi(argv[1]));
    char top[M], cur[M], tmp[M];
    getcwd(top,M);
    printf("top=%s\n",top);
    strncpy(cur, ".", M);
    for(i=0; i<n; i++) {
        strncpy(tmp, cur, M);
        snprintf(cur, M, "%s/Foo", tmp);
        mkdir(cur, 0755);
        snprintf(tmp, M, "%s/Foo_%d", top, i);
        symlink(cur, tmp);
    }
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
