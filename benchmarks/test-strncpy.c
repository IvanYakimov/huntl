#include "built-in.h"
#include "string.c"

void gen_strncmp(const char *cs, const char *ct, size_t count, int res);

void test_1() {
	const buff_size = 4;
	char buff1[buff_size];
	char buff2[buff_size];
	init_buff(buff1, buff_size);
	init_buff(buff2, buff_size);
	size_t count = mksym_u64();
	limit2_u64(&count, 0, buff_size - 1);
	int res = strncmp(buff1, buff2, count);
	gen_strncmp(buff1, buff2, count, res);
}
