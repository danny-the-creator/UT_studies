#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

void dash(void);

void underscore(void);

int main(int argc, char** argv)
{
    setbuf (stdout, NULL);	
    printf ("Executing both functions\n");

    dash();
    underscore();
  
    return EXIT_SUCCESS;
}


void dash(void) 
{
    int i;
    char c1 = '-';
    
    for (i = 1; i <= 250; i++) {
        write (1, &c1, 1);
    }
}


void underscore(void) 
{
    int i;
    char c1 = '_';
    
    for (i = 1; i <= 250; i++) {
        write (1, &c1, 1);
    }
}
