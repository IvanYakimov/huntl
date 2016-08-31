#include "lib-string.c"

void gen_strtobool(const char *s, bool *res, int r);

void test_strtobool() {
	char s;
	bool val;
	int r = strtobool(&s,&val);
	gen_strtobool(&s,&val,r);
}
