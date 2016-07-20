#include "built-in.h"

void gen_ptr(int x, int r);
int ptr(int ***x) {
	return ***x;
}

void test_1() {
	int a = 0, r = 0;
	a = 28;
	int *a_ptr = &a;
	int **a_ptr_ptr = &a_ptr;
	int ***a_ptr_ptr_ptr = &a_ptr_ptr;
	r = ptr(a_ptr_ptr_ptr);
	gen_ptr(a,r);
}
