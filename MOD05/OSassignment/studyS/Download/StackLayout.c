/*  StackLayout.c - Discover the stack layout by printing the stack of three
    nested calls. The stack grows from high to low addresses. Within a
    stack frame the argument declared last is stored at the lowest address
    and the local variable declared first sits at the highest address. */

#include <stdio.h>
// #include <stdint.h>
#include <inttypes.h>

#define PRIxPTR_WIDTH sizeof(size_t)*2

#define N 8
size_t *q;

static inline void *align(void *p) {
    uintptr_t align = sizeof(size_t);
    uintptr_t addr  = (uintptr_t)p;
    addr = addr & ~(align-1);
    return (void*)addr;
}

void bar(int e, int f) {
    int g = 0x1010, h = 0x0101;
    size_t *p;
    printf("%p:e\n%p:f\n%p:g\n%p:h\n%p:p\n\nStack memory dump:\n", (void *) &e, (void *) &f, (void *) &g, (void *) &h, (void *) &p);
    /*
    printf("s/%p/&:e/\ns/%p/&:f/\ns/%p/&:g/\ns/%p/&:h/\ns/%p/&:p/\n",
        (void *) &e, (void *) &f, (void *) &g, (void *) &h, (void *) &p);
    */
    for(p=align(&f-N);p<=q;p++){
        //printf("#%p\t%0zx\n", (void *) p, *p);
        printf("%p  %0*" PRIxPTR "\n", (void *) p, PRIxPTR_WIDTH, *p);
        
    }
}

void foo(size_t c, size_t d) {
    printf("%p:c\n%p:d\n", (void *) &c, (void *) &d);
    bar(0xeeee,0xffff);
}

int main(int argc, char * argv[], char *envp[]) {
    int a = 0xaaaa, b = 0xbbbb;
    printf("Stack:\n%p:argc\n%p:argv\n%p:envp\n%p:a\n%p:b\n",
        (void *) &argc, (void *) &argv, (void *) &envp, (void *) &a, (void *) &b);
    q = align(&a+N);
    foo(0xcccc,0xdddd);
    // printf("#%p:bar\n#%p:foo\n#%p:main\n#%p:q\n", &bar, &foo, main, (void *) &q);
    printf("\nText, Data, BSS:\n%p:bar\n%p:foo\n%p:main\n%p:q\n\n", &bar, &foo, &main, (void *) &q);
    return 0;
}
