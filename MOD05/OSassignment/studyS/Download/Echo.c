/*  Echo.c - print the command line arguments (if any) */

#include <stdio.h>

int main(int argc, char *argv[]) {
    int i;
    for(i=0; i < argc; i++) {
        printf("%s ", argv[i]);
    }
    printf("(%d)\n", argc);
    return 0;
}
