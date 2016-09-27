/* Start. Some mocked externals */

#undef NULL
#undef true
#undef false
#undef EINVAL

#define NULL 0
#define true 1
#define false 0
#define EINVAL 22

#undef u64
#undef u8
#undef size_t
#undef ssize_t
#undef bool
typedef unsigned long u64;
typedef unsigned char u8;
typedef unsigned long size_t;
typedef long  ssize_t;
typedef char bool;

#undef isupper
#undef islower
#undef isspace
bool isupper(char c);
bool islower(char c);
bool isspace(char c);

#undef tolower
#undef toupper
#undef BUG_ON
static inline unsigned char tolower(unsigned char c);
static inline unsigned char toupper(unsigned char c);
void BUG_ON(bool predicate);
/* End. */

// test-strcmp.c (comparison)
int strcmp(const char *cs, const char *ct);
int strncmp(const char *cs, const char *ct, size_t count);
int strcasecmp(const char *s1, const char *s2);
int strncasecmp(const char *s1, const char *s2, size_t len);
bool sysfs_streq(const char *s1, const char *s2);

// test-strcpy.c (copying)
char *strcpy(char *dest, const char *src);
char *strncpy(char *dest, const char *src, size_t count);
size_t strlcpy(char *dest, const char *src, size_t size);

// test-strcat.c (concatenation)
char *strcat(char *dest, const char *src); 
char *strncat(char *dest, const char *src, size_t count);
size_t strlcat(char *dest, const char *src, size_t count);

// test-strchr.c (searching for characters)
char *strchr(const char *s, int c); 
char *strchrnul(const char *s, int c); 
char *strrchr(const char *s, int c); 
char *strnchr(const char *s, size_t count, int c); 

// test-strlen.c	(measurment)
size_t strlen(const char *s); 
size_t strnlen(const char *s, size_t count);
size_t strspn(const char *s, const char *accept);
size_t strcspn(const char *s, const char *reject);

// test-str.c (searching)
char *strstr(const char *s1, const char *s2);
char *strnstr(const char *s1, const char *s2, size_t len);
char *strpbrk(const char *cs, const char *ct);
int match_string(const char * const *array, size_t n, const char *string);

// test-transform.c (transformation)
char *skip_spaces(const char *str);
char *strim(char *s);
char *strreplace(char *s, char old, char new);
char *strsep(char **s, const char *ct);

// no testing for void* functions yet
void *memset(void *s, int c, size_t count);
void *memcpy(void *dest, const void *src, size_t count);
void *memmove(void *dest, const void *src, size_t count);
int memcmp(const void *cs, const void *ct, size_t count);
void *memscan(void *addr, int c, size_t size);
void *memchr(const void *s, int c, size_t n);
void *memchr_inv(const void *start, int c, size_t bytes);
static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes);










