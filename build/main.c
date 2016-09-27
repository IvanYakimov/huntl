#include <stdio.h>
#include "../benchmarks/lib/string/string.c"

void test__strcmp() {
  char s1[6] = "xuwet",
    s2[6] = "xuwea";
  int res = strcmp(s1,s2);
  printf("strcmp: &\"%s\" &\"%s\" :=> %d\n", s1, s2, res);
}

void test__strncmp() {
  char s1[6] = "ogfo",
    s2[6] = "ogfo";
  int res = strncmp(s1,s2,5);
  printf("strcmp: &\"%s\" &\"%s\" %d :=> %d\n", s1, s2, 5, res);
}

void test__sysfs_streq() {
  char s1[6] = "vu\n\0b",
    s2[6] = "vuely";
  int res = sysfs_streq(s1,s2);
  printf("sysfs_streq: &\"%s\" &\"%s\" :=> %d\n", s1, s2, res);
}

void test__strcat() {
  char s1[10] = "xoha",
    s2[5] = "joq",
    s1_original[10];
  strcpy(s1_original, s1);
  strcat(s1, s2);
  printf("strcat: &\"%s\" &\"%s\" :=> &\"%s\"\n", s1_original, s2, s1);
}

void test__strncat() {
  char s1[10] = "yxr",
    s2[5] = "yop",
    s1_original[10];
  strcpy(s1_original, s1);
  strncat(s1, s2, 4);
  printf("strcat: &\"%s\" &\"%s\" %d :=> &\"%s\"\n", s1_original, s2, 4, s1);
}

void test__strcpy() {
  char s1[6] = "lee",
    s2[6] = "dwuk",
    s1_or[6];
  strcpy(s1_or, s1);
  strcpy(s1, s2);
  printf("strcat: &\"%s\" &\"%s\" :=> &\"%s\"\n", s1_or, s2, s1);
}

void test__strncpy() {
  char s1[6] = "lydv",
    s2[6] = "myn",
    s1_or[6];
  strcpy(s1_or, s1);
  strncpy(s1, s2, 5);
  printf("strncat: &\"%s\" &\"%s\" %d :=> &\"%s\"\n", s1_or, s2, 4, s1);
}

void test__strlen() {
  char s[6] = "xupg";
  int res = strlen(s);
  printf("strlen: &\"%s\" :=> %d\n", s, res);
}

void test__strnlen() {
  char s[6] = "ngsa";
  int res = strnlen(s, 6);
  printf("strnlen: &\"%s\" %d :=> %d\n", s, 6, res);
}

void test__strstr() {
  char s1[6] = "risa",
    s2[3] = "i";
  char *p = strstr(s1,s2);
  printf("strstr: &\"%s\" &\"%s\" :=> &\"%s\"\n", s1, s2, p);
}

void test__strnstr() {
  char s1[6] = "qbumn",
    s2[6] = "b";
  char *p = strnstr(s1, s2, 2);
  printf("strnstr: &\"%s\" &\"%s\" %d :=> &\"%s\"\n", s1, s2, 2, p);
}

void test__strpbrk() {
  char s1[6] = "taotl",
    key[6] = "aeiou";
  char *res = strpbrk(s1, key);
  printf("strpbrk: &\"%s\" &\"%s\" :=> &\"%s\"\n", s1, key, res);
}

int main() {
  test__strcmp();
  test__strncmp();
  test__sysfs_streq();
  test__strcat();
  test__strncat();
  test__strcpy();
  test__strncpy();
  test__strlen();
  test__strnlen();
  test__strstr();
  test__strnstr();
  test__strpbrk();
}
