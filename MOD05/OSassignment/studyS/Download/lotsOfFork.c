#include <stdio.h>
#include <unistd.h>

int main(int argc, char** argv) {
        pid_t c = 0;
        while (c != -1) {
                c = fork();
        }
        printf("cannot fork anymore\n");
        return 0;
}
