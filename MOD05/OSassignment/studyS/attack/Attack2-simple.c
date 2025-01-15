#include <stdio.h>
#include <stdlib.h>

void secret() {
  system("cat /etc/passwd");
  return;
}

void update(int * table) {
  int toAdd = 0;
  int candidate = 0;
  printf("Which lecture?\n");
  scanf("%d", &candidate);
  printf("How many votes?\n");
  scanf("%d", &toAdd);
  table[candidate-1] += toAdd;
  return;
}

void loop() {
  int candidates[2] = {0,0};
  while(1) {
    printf("Current votes:\n1 - Operating Systems: %d\n2 - Computer Architecture: %d\n", candidates[0], candidates[1]);
    update(candidates);
  }
  return;
}

int main(int argc, char** argv) {
  loop();
}