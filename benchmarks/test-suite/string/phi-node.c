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

int select(int x, int y) {
	int r = x < y ? 3 : 7;
	return r;
}
void gen_select(int x, int y, int r);
void test_SELECT() {
	int x = 0, y = 2;
	//int z = x < y ? 3 : 7;
	int r = select(x, y);
	gen_select(x, y, r);
}










