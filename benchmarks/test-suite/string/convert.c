#include "../../lib/llvoyager/built-in.h"
#include "../../lib/lib-string.c"

#warning "switch-case instruction must be implemented"

void gen_strtobool(const char *s, bool *res, int r);

void test_strtobool() {
	char s;
	bool val;
	int r = strtobool(&s,&val);
	gen_strtobool(&s,&val,r);
}
