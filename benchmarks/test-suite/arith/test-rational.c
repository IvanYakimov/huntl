#include "built-in.h"
#include "sym-limits.h"
#include <limits.h>

#include "rational.c"

unsigned long rational_best_approximation(
	unsigned long given_numerator, unsigned long given_denominator,
	unsigned long max_numerator, unsigned long max_denominator,
	unsigned long *best_numerator, unsigned long *best_denominator);

void gen_rational_best_approximation(
	unsigned long given_numerator, unsigned long given_denominator,
	unsigned long max_numerator, unsigned long max_denominator,
	unsigned long *best_numerator, unsigned long *best_denominator,
	unsigned long res);

void test_rational() {
	unsigned long num = 2;
	unsigned long den = 4;
	unsigned long max_num = 100;
	unsigned long max_den = 100;
	unsigned long best_num = 0;
	unsigned long best_den = 0;
	num = mksym_u64();
	//den = mksym_u64();
	limit2_u64(&num,1,4);
	//limit2_u64(&den,2,6);
	unsigned long status = rational_best_approximation(num, den, max_num, max_den, &best_num, &best_den);
	gen_rational_best_approximation(num, den, max_num, max_den, &best_num, &best_den, status);
}







