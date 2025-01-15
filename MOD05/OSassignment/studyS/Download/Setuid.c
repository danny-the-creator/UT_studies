/*  Setuid.c - Reduce privilege when doing something dangerous

    lecturer:
        /bin/rm -rf /tmp/db /tmp/submit
        mkdir /tmp/db
        chmod 700 /tmp/db
        gcc '-DDIR="/tmp/db/"' Setuid.c -o /tmp/submit
        chmod +s /tmp/submit
        /tmp/submit <Answer.txt

    student:
        /tmp/submit <Assignment.txt
*/

#include <stdio.h>
#include <unistd.h>

#define N 16

int main(int argc, char * argv[]) {
    char fn[N], buf[N];
    uid_t id = getuid();
    printf("rid=%d, eid=%d\n", id, geteuid());
    snprintf(fn, N, "%s/%d", DIR, id);
    FILE *fp = fopen(fn, "w");
    setreuid(id, id);
    printf("rid=%d, eid=%d\n", getuid(), geteuid());
    fflush(stdout);
    while (gets(buf) != 0) {
        fputs(buf,fp);
        fputc('\n',fp);
    }
    fclose(fp);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
