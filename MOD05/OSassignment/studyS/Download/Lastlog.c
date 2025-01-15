/*  Lastlog.c - print the name of the line, system, date and time from
    the last login of the users passed as command line arguments. */

#include <time.h>
#include <lastlog.h>
#include <stdio.h>
#include <pwd.h>
#include <stdlib.h>

#define llsz sizeof(struct lastlog)

int main(int argc, char *argv[]) {
    FILE *fp=fopen("/var/log/lastlog", "r");
    int i;
    for(i=1;i<argc;i++) {
        struct passwd *p = getpwnam(argv[i]);
        if(p == NULL) {
            printf("unknown user: %s\n", argv[i]);
        } else {
            struct lastlog ll;
            fseek(fp, p->pw_uid*llsz, 0);
            fread(&ll, llsz, 1, fp);
            time_t t = ll.ll_time;
            /* printf("sizeof(t)=%ld, sizeof(ll.ll_time)=%ld\n", sizeof(t), sizeof(ll.ll_time)); */
            printf("%s %s %s %s", argv[i], ll.ll_line,
                ll.ll_host, ctime(&t));
        }
    }
    fclose(fp);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
