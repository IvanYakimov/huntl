#include "built-in.h"
#include "string.c"

#warning "strXstr methods are hide as they do not work"
void gen_strstr(const char *s1, const char *s2, char *res);
void test_strstr() {
	const size_t s1_len = 6, s2_len = 3;
	char s1[s1_len], s2[s2_len];
	init_buff(s1, s1_len); init_buff(s2, s2_len);
	char *res = strstr(s1, s2);
	gen_strstr(s1, s2, res);
}

void gen_strnstr(const char *s1, const char *s2, size_t len, char *res);
void test_strnstr() {
	const size_t s1_len = 6, s2_len = 3;
	char s1[s1_len], s2[s2_len];
	init_buff(s1, s1_len); init_buff(s2, s2_len);
	char *res = strnstr(s1, s2, s2_len-1);
	gen_strnstr(s1, s2, s2_len-1, res);
}

void gen_strpbrk(const char *cs, const char *ct, char *res);
void test_strprk() {
	const size_t str_size = 6, key_size = 6;
	char str[str_size], key[key_size];
	init_buff(str, str_size); //init_buff(key, ct_size);
	key[0] = 'a'; key[1] = 'e'; key[2] = 'i'; key[3] = 'o'; key[4] = 'u'; key[5] = '\0';
	char *res = strpbrk(str, key);
	gen_strpbrk(str, key, res);
}

#warning "match_string: getelementptr needs to be fully supported"
/*
void gen_match_string(const char * const *array, size_t n, const char *string, int res);
void test_match_string() {
	const size_t count = 4, len = 5;
	char arr[count][len];
	for (size_t n = 0; n < count; ++n)
		init_buff(arr[n], len);
}
*/















