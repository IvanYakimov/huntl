#include "built-in.h"
#include "hweight.c"
#include "sym-limits.h"

//TODO: replace by macro OR generate
unsigned int gen___sw_hweight32(unsigned int w, unsigned int res) {}
unsigned int gen___sw_hweight16(unsigned int w, unsigned int res) {}
unsigned int gen___sw_hweight8(unsigned int w, unsigned int res) {}
unsigned long gen___sw_hweight64(__u64 w, __u64 res) {}

int test_1() {
	unsigned int w;
	unsigned int res;
	w = mksym_u32();
	w = limit_u32(w, 0,63);
	res = 0;
	res = __sw_hweight32(w);
	gen___sw_hweight32(w,res);
	return 0;
}

int test_2() {
	unsigned int w;
	unsigned int res;
	w = mksym_u32();
	w = limit_u32(w, 0,63);
	res = 0;
	res = __sw_hweight8(w);
	gen___sw_hweight8(w,res);
	return 0;
}

int test_3() {
	unsigned int w;
	unsigned int res;
	w = mksym_u32();
	w = limit_u32(w, 0,63);
	res = 0;
	res = __sw_hweight16(w);
	gen___sw_hweight16(w,res);
	return 0;
}

//TODO: implement sext and zext
/*
int test_2() {
	__u64 w;
	__u64 res;
	w = mksym_u64();
	res = 0;
	res = __sw_hweight64(w);
	gen___sw_hweight64(w,res);
	return 0;
}
*/
