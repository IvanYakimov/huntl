/* Start. Some mocked externals */
#define NULL 	0
#define true 	1
#define false 	0
#define EINVAL 	22
typedef unsigned long 	u64;
typedef unsigned char 	u8;
typedef unsigned long 	size_t;
typedef long 			ssize_t;
typedef char 			bool;

bool isupper(char c);

bool islower(char c);

bool isspace(char c);
static inline unsigned char tolower(unsigned char c);
static inline unsigned char toupper(unsigned char c);
void BUG_ON(bool predicate);
/* End. */

int strncasecmp(const char *s1, const char *s2, size_t len);	//
int strcasecmp(const char *s1, const char *s2);					// required phi-node
char *strcpy(char *dest, const char *src);						// DONE.
char *strncpy(char *dest, const char *src, size_t count);		// fails sometime
size_t strlcpy(char *dest, const char *src, size_t size);
char *strcat(char *dest, const char *src);						// fails
char *strncat(char *dest, const char *src, size_t count);
size_t strlcat(char *dest, const char *src, size_t count);
int strcmp(const char *cs, const char *ct);						// required select
int strncmp(const char *cs, const char *ct, size_t count);
char *strchr(const char *s, int c);								// fails sometime
char *strchrnul(const char *s, int c);							// required phi-node
char *strrchr(const char *s, int c);							//
char *strnchr(const char *s, size_t count, int c);				// required phi-node
char *skip_spaces(const char *str);
char *strim(char *s);
size_t strlen(const char *s);									// DONE.
size_t strnlen(const char *s, size_t count);
size_t strspn(const char *s, const char *accept);
size_t strcspn(const char *s, const char *reject);
char *strpbrk(const char *cs, const char *ct);
char *strsep(char **s, const char *ct);
bool sysfs_streq(const char *s1, const char *s2);
int match_string(const char * const *array, size_t n, const char *string);
void *memset(void *s, int c, size_t count);
void *memcpy(void *dest, const void *src, size_t count);
void *memmove(void *dest, const void *src, size_t count);
int memcmp(const void *cs, const void *ct, size_t count);
void *memscan(void *addr, int c, size_t size);
char *strstr(const char *s1, const char *s2);
char *strnstr(const char *s1, const char *s2, size_t len);
void *memchr(const void *s, int c, size_t n);
static void *check_bytes8(const u8 *start, u8 value, unsigned int bytes);
void *memchr_inv(const void *start, int c, size_t bytes);
char *strreplace(char *s, char old, char new);
