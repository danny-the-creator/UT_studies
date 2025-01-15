/* Uname.c */
#include <stdio.h>
#include <sys/utsname.h>

int main(int argc, char * argv[]) {
    struct utsname u;
    if(uname(&u) == 0) {
        printf("%s %s %s %s\n",
            u.nodename, u.sysname,
            u.release, u.machine);
    }
    return 0;
}
