#include "built-in.h"
#include "gcd.c"

//TODO: replace by macro OR generate
unsigned long gen_gcd(unsigned long a, unsigned long b, unsigned long res) {}

int test_gcd() {
	unsigned long a = 0;
	unsigned long b = 0;
	unsigned long r = 0;
	a = mksym_u64();
	b = mksym_u64();
	limit2_u64(&a, 0, 8);
	limit2_u64(&b, 0, 16);
	r = gcd(a,b);
	gen_gcd(a,b,r);
	return 0;
}
