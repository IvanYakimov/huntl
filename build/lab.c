#include <stdint.h>
typedef uint64_t Name;

int f(int x, int y) {
  int z = x + y;
  return z;
}

int main() {
  return f(0,1);
}
