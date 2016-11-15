#include "built-in.h"

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
	x = mksym_i32();
	y = mksym_i32();
	//int z = x < y ? 3 : 7;
	int r = select(x, y);
	gen_select(x, y, r);
}

int the_switch(int key) {
	switch (key) {
	case 1:
		return 10;
	case 2:
		return 20;
	case 3:
		return 30;
	default:
		return 42;
	}
}
void gen_the_switch(int key, int res);
void test_the_switch() {
	int key = 1;
	int res = the_switch(key);
	gen_the_switch(key, res);
}







