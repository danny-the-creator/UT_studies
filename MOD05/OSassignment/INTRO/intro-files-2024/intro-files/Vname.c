/* Vname.c */
#include <stdio.h>
#include <stdlib.h>
#include <sys/utsname.h>

int main(int argc, char * argv[]) {
    struct utsname *v = malloc(sizeof(struct utsname));
    if(uname(v) == 0) {
        printf("%s %s %s %s\n",
            v->nodename, v->sysname,
            v->release, v->machine);
    }
    return 0;
}
