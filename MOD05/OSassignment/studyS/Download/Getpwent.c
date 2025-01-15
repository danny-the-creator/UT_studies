/*  Getpwent.c - List all user accounts on the system */

#include <stdio.h>
#include <pwd.h>

int main(int argc, char* argv[]) {
    struct passwd *p;
    endpwent();
    while ((p = getpwent()) != NULL) {
        printf("%s:%s:%d:%d:%s:%s:%s\n",
           p->pw_name,
           p->pw_passwd,
           p->pw_uid,
           p->pw_gid,
           p->pw_gecos,
           p->pw_dir,
           p->pw_shell);
    }
    endpwent();
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
