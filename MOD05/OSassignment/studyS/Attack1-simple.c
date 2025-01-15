#include <stdio.h>
#include <stdlib.h>

void secret() {
  system("cat /etc/passwd");
  return;
}

void readStdin() {
  char buf[18];
  gets(buf);
  return;
}

void readLine() {
    return readStdin();
}

int main(int argc, char** argv) {
  readLine();
  printf("Nothing happened\n");
  return 0;
}