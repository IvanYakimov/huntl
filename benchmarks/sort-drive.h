#include "built-in.h"

int* sort(int array[], int n);
void gen_sort(int origin[], int n, int res[]);
void test_sort() {
  const int len = 4;
  int arr[len],
    origin[len],
    *res;
  init_int_buff(arr, len);
  cpy_int_buff(origin, arr, len);
  res = sort(arr, len);
  gen_sort(origin, len, res);
}
