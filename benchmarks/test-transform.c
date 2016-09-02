#include "built-in.h"
#include "string.c"


#warning "skip_spaces: fails into an infinite loop!"
/*
void gen_skip_spaces(const char *str, char *res);
void test_skip_spaces() {
	const size_t size = 6;
	char str[size], origin[size];
	init_buff(str, size);
	//str[0] = 'h'; str[1] = 'e'; str[2] = 'l'; str[3] = 'l'; str[4] = 'o'; str[5] = '\0';
	strcpy(origin, str);
	char *res = skip_spaces(str);
	gen_skip_spaces(origin, res);
}
char *strim(char *s);
*/

//char *strreplace(char *s, char old, char new);
void gen_strreplace(char *s, char old, char new, char *res);
void test_strreplace() {
	const size_t len = 6;
	char str[len], str_[len],
	old = mksym_i8(),
	new = mksym_i8();
	init_buff(str, len);
	//str[0] = 'h'; str[1] = 'e'; str[2] = 'l'; str[3] = 'l'; str[4] = 'o'; str[5] = '\0';
	strcpy(str_, str);
	char *res = strreplace(str, old, new);
	gen_strreplace(str_, old, new, res);
}

#warning "strsep: getelementptr needs to be improved (array of pointer support)"
char *strsep(char **s, const char *ct);













