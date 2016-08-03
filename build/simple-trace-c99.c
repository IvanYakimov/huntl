#include <stdio.h>
#include <stdlib.h>

//-------------------------------------------------------------------------------
//               TEST_3 example

/* C source:
void test_3() {
	int x = 99;
	int *y = &x;
	*y = 28;
	int result = x;
}
 */

/* IR code:
define void @test_3() #0 {
  %x = alloca i32, align 4
  %y = alloca i32*, align 8
  %result = alloca i32, align 4
  store i32 99, i32* %x, align 4
  store i32* %x, i32** %y, align 8
  %1 = load i32** %y, align 8
  store i32 28, i32* %1, align 4
  %2 = load i32* %x, align 4
  store i32 %2, i32* %result, align 4
  ret void
}
 */

// C representation for the IR code
void test_3() {
  int *t1 = 0; int t2 = 0;
  // %x = alloca <i32>, align 4
  int *x = alloca(sizeof(int*));
  // %y = alloca <i32>*, align 8
  int **y = alloca(sizeof(int**));
  // %result = alloca i32, align 4
  int *result = alloca(sizeof(int*));
  // store i32 99, i32* %x, align 4
  *x = 99;
  // store i32* %x, i32** %y, align 8
  *y = x;
  //%1 = load i32** %y, align 8
  t1 = *y;
  // store i32 28, i32* %1, align 4
  *t1 = 28;
  //%2 = load i32* %x, align 4
  t2 = *x;
  // store i32 %2, i32* %result, align 4
  *result = t2;
  // ret void
  printf("%d\n",*result);
}

//-------------------------------------------------------------------------------
//               TEST_4 example

/* C source:
void test_4() {
	int x = 42;
	int y = x;
}
 */

/* IR source:
define void @test_4() #0 {
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 42, i32* %x, align 4
  %1 = load i32* %x, align 4
  store i32 %1, i32* %y, align 4
  ret void
}
 */

void test_4() {
  int t1;
  // %x = alloca i32, align 4
  int *x = alloca(sizeof(int*));
  // %y = alloca i32, align 4
  int *y = alloca(sizeof(int*));
  // store i32 42, i32* %x, align 4
  *x = 42;
  // %1 = load i32* %x, align 4
  t1 = *x;
  // store i32 %1, i32* %y, align 4
  *y = t1;
  // ret void
  printf("%d\n", *y);
}

//-------------------------------------------------------------------------------
//               MAIN (RUNNER)

int main() {
  test_3();
  test_4();
}
