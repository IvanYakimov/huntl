#include "../../lib/llvoyager/built-in.h"

int func(int y, int z) {
	return y && z;
}

void gen_func(int y, int z, int res);
void test_AND() {
	int res = 0, y = 0, z = 0;
	y = mksym_i32();
	z = mksym_i32();
	res = func(y, z);
	gen_func(y, z, res);
}

void test_SELECT() {
	int x = 0, y = 2;
	int z = x < y ? 1 : 2;
}
