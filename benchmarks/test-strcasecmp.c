#include "built-in.h"
#include "string.c"

#ifndef PHI_NODE
#error "phi node needs to be implemented"
#endif

void gen_strcasecmp(const char *s1, const char *s2, int res);

test_strcasecmp() {
	char buf1[10];
	char buf2[10];
	init_buff(buf1, 10);
	init_buff(buf2, 10);
	int res = strcasecmp(buf1, buf2);
}
