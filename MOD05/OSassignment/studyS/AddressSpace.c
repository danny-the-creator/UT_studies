/*  AddressSpace.c - Discover the address space layout by printing
    relevant addresses in the stack, data and bss segments */

#include <stdio.h>
#include <stdlib.h>
#include <alloca.h>
#include <unistd.h>

extern char etext, edata, end;
int a = 0xaaaa, b;

int main(int argc, char * argv[]) {
    int i, c = 0xcccc;
    int *d_ptr = (int*) malloc(sizeof(int));
    int *e_ptr = (int*) alloca(sizeof(int));
    b = 0xbbbb;
    *d_ptr = 0xdddd;
    *e_ptr = 0xeeee;
    printf("%p:main\n", &main);
    printf("%p:etext\n\n", &etext);
    printf("%p:a=%0x\n", (void *) &a, a);
    printf("%p:edata\n\n", &edata);
    printf("%p:b=%0x\n", (void *) &b, b);
    printf("%p:end\n\n", &end);
    printf("%p:d=%0x\n", (void *) d_ptr, *d_ptr);
    printf("%p:brk\n\n", sbrk(0));
    for(i = 1; i <= 8192; i++) {
        d_ptr = (int*) malloc(sizeof(int));
        *d_ptr = 0xdddd;
    }
    printf("%p:d=%0x\n", (void *) d_ptr, *d_ptr);
    printf("%p:brk\n\n", sbrk(0));
    printf("%p:e=%0x\n", (void *) e_ptr, *e_ptr);
    printf("%p:argc=%0x\n", (void *) &argc, argc);
    printf("%p:c=%0x\n", (void *) &c, c);
    return 0;
}

/*  Please note that the checks on the return value of the system calls
    have been omitted to avoid cluttering the code. However, system calls
    can and will fail, in which case the results are unpredictable. */
