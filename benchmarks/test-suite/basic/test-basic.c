#include "built-in.h"
#include "sym-limits.h"
#include "basic.c"

#include <limits.h>

//--------------------------------------------------------------------
// <-- Conversions

void gen_extend(short x, int res);
int extend(short x) {
	return (int)x;
}

void test_extend() {
	short arg = 28;
	int res = 0;
	arg = mksym_i16();
	limit2_i16(&arg, SHRT_MIN, SHRT_MAX);
	res = extend(arg);
	gen_extend(arg, res);
}

void gen_truncate(long x, unsigned int res);
unsigned int truncate(long x) {
	return (unsigned int)x;
}

void test_truncate() {
	long arg = 28;
	unsigned res = 0;
	arg = mksym_i64();
	limit2_i64(&arg, LONG_MIN, LONG_MAX);
	res = truncate(arg);
	gen_truncate(arg, res);
}

void gen_conv(short a, long b, int r);
int conv(short x, long y) {
	return (int)x + (int)y;
}

void test_conv() {
	short a = 28;
	long b = 42;
	int r = 0;
	a = mksym_i16();
	limit2_i16(&a, SHRT_MIN, SHRT_MAX);
	b = mksym_i64();
	limit2_i64(&b, LONG_MIN, LONG_MAX);
	r = conv(a, b);
	gen_conv(a, b, r);
}

// -->
//--------------------------------------------------------------------

//TODO: replace by macro OR generate
void gen_eq(int x, int y, int r);
int eq(int x, int y) {
	if (x == y)
		return 1;
	else 
		return 0;
}

void test_eq() {
	int a = 12, b = 42,
		 r = 28;
	a = mksym_i32();
	b = mksym_i32();
	limit2_i32(&a, INT_MIN, INT_MAX);
	limit2_i32(&b, INT_MIN, INT_MAX);
	r = eq(a,b);
	gen_eq(a,b,r);
}

void gen_arith(int x, int y, int r);
int arith(int x, int y) {
	if (x - y == 0)
		return 1;
	else
		return -1;
}

void test_mixed_arith() {
	int a = 0, b = 0, r = 0;
	a = mksym_i32();
	b = mksym_i32();
	limit2_i32(&a, INT_MIN, INT_MAX);
	limit2_i32(&b, INT_MIN, INT_MAX);
	r = arith(a,b);
	gen_arith(a,b,r);
}

void gen_sum(int a, int n, int r);
int sum(int a, int n) {
	int i = 0, s = 0;
	for (i = 0; i < n; i++)
		s += a;
	return s;
}

void test_sum() {
	int a = 0, n = 0, s = 0;
	a = mksym_i32();
	n = mksym_i32();
	limit2_i32(&a,0,3);
	limit2_i32(&n,0,4);
	s = sum(a,n);
	gen_sum(a,n,s);
}

void gen_recsum(unsigned a, unsigned n, unsigned res);
unsigned recsum(unsigned a, unsigned n) {
	if (n == 1)
		return a;
	else
		return a + recsum(a, n - 1);
}

void test_recsum() {
	int a = 2, n = 4, s = 0;
	a = mksym_i32();
	//n = mksym_i32();
	limit2_i32(&a,0,3);
	//limit2_i32(&n,0,3);
	s = recsum(a,n);
	gen_recsum(a,n,s);
}

//TODO: switch-case support
/*
int gen_cases(int k, int r);
int cases(int k) {
	switch (k) {
		case 1: return -1;
		case 2: return -2;
		case 3: return -3;
		default: return 0;
	}
}

int test_cases() {
	int k = 0, r = 0;
	k = mksym_i32();
	r = cases(k);
	gen_cases(k,r);
	return 0;
}
*/















