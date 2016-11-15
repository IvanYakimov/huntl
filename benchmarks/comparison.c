#include "built-in.h"
#include "string.c"

#warning "strcmp: select required & fails sometimes"
void gen_strcmp(const char *cs, const char *ct, int res);
void test_strcmp() {
	const size_t len = 6;
	char s1[len], s2[len];
	init_buff(s1, len); init_buff(s2, len);
	int res = strcmp(s1,s2);
	gen_strcmp(s1,s2,res);
}

#warning "strncmp: fails sometimes"
void gen_strncmp(const char *cs, const char *ct, size_t count, int res);
void test_1() {
	const size_t len = 6;
	char s1[len], s2[len];
	init_buff(s1, len);
	init_buff(s2, len);
	int res = strncmp(s1, s2, len-1);
	gen_strncmp(s1, s2, len-1, res);
}

/*
#warning "strcasecmp: fails everytime, phi node required!"
void gen_strcasecmp(const char *s1, const char *s2, int res);
void test_strcasecmp() {
	const size_t len = 4;
	char s1[len], s2[len];
	init_buff(s1, len); init_buff(s2, len);
	s1[0] = 'B'; s1[1] = 'y'; s1[2] = 'e'; s1[3] = '\0';
	int res = strcasecmp(s1, s2);
	gen_strcasecmp(s1,s2,res);
}

#warning "strncasecmp: fails sometime Load()-ended call-chain: visitZExtInst -> HandleZExtInst -> ProduceHolder -> Load"
void gen_strncasecmp(const char *s1, const char *s2, size_t len, int res);
void test_strncasecmp() {
	const size_t len = 4;
	char s1[len], s2[len];
	init_buff(s1, len); init_buff(s2, len);
	s1[0] = 'B'; s1[1] = 'y'; s1[2] = 'e'; s1[3] = '\0';
	int res = strncasecmp(s1, s2, len-1);
	gen_strncasecmp(s1,s2,len-1,res);
}
*/

#warning "sysfs_streq: doesn't work"
void gen_sysfs_streq(const char *s1, const char *s2, bool res);
void test_sysfs_streq() {
	const size_t size = 6;
	char s1[size], s2[size];
	init_buff(s1, size); init_buff(s2, size);
	bool res = sysfs_streq(s1, s2);
	gen_sysfs_streq(s1, s2, res);
}













