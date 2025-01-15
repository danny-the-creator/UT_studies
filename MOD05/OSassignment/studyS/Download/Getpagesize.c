/*  Getpagesize.c - ask the system about the page size */

#include <stdio.h>
#include <unistd.h>

int main() {
    printf("pagesize=%d\n", getpagesize());
    return 0;
}
