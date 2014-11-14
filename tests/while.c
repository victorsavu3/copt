#include "stdio.h"

int main() {
  int n = 5;
  int a = 1;
  int i = 0;
  while(i < n) {
    i++;
    a *= i;
  }
  printf("fib(%i) = %i\n", n, a);
}
