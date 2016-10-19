#include <stdint.h>
#include <stdio.h>

int main() {
  int a = 28, b = 42, res = 57;
  a += 101;
  if (a < b)
    res = a;
  else
    res = b;
}
