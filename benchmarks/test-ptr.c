#include "built-in.h"
#include "sym-limits.h"

int ptr_helper(int **y) {
	if (**y == 28)
		return 2;
	else if (**y == 42)
		return 4;
	else
		return -13;
}

void gen_ptr(int x, int r);
int ptr(int x) {
	int *z = &x;
	return ptr_helper(&z);
}

void test_1() {
	int a = 0, r = 0;
	a = mksym_i32();
	r = ptr(a);
	gen_ptr(a,r);
}
