#include "string.c"
#include "built-in.h"

void gen_match_wildcard(const char *pattern, const char *str, bool res);
void test_match_wildcard() {
	size_t p_len = 3, s_len = 6;
	char pattern[p_len], str[s_len];
	init_buff(pattern, p_len); init_buff(str, s_len);
	bool res = match_wildcard(pattern, str);
	gen_match_wildcard(pattern, str, res);
}
