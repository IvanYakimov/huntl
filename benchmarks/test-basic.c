#include "built-in.h"
#include "sym-limits.h"
#include "basic.c"

//TODO: replace by macro OR generate
void gen_eq(int x, int y, int r);
int eq(int x, int y) {
	if (x == y)
		return 1;
	else 
		return 0;
}

void test_1() {
	int a = 0, b = 0,
		 r = 0;
	a = mksym_i32();
	b = mksym_i32();
	a = limit_i32(a,-10,10);
	b = limit_i32(b,-10,10);
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
	a = limit_i32(a,-10,10);
	b = limit_i32(b,-10,10);
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
	//TODO: make as a macro:
	a = limit_i32(a,0,3);
	n = limit_i32(n,0,4);
	//end
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
	int a = 0, n = 0, s = 0;
	a = mksym_i32();
	n = mksym_i32();
	//TODO: make as a macro:
	a = limit_i32(a,0,3);
	n = limit_i32(n,0,4);
	//end
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















