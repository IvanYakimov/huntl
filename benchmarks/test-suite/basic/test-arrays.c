#include "built-in.h"
#include "sym-limits.h"
#include <limits.h>

void gen_arr1(int x, int r);
int arr1(int x) {
	const int len = 10;
	int arr[len];
	int sum = 0;
	for (int i = 0; i < len; ++i) {
		arr[i] = i;
		sum += arr[i];
	}
	return arr[x] * sum;
}
void test_arr1() {
	int a = 5, r = 0;
	r = arr1(a);
	gen_arr1(a,r);
}

void gen_sum(int x0, int x1, int x3, int r);
int sum(int x0, int x1, int x2) {
	int arr[3]; int sum = 0;
	arr[0] = x0; arr[1] = x1; arr[2] = x2;
	for (int i = 0; i < 3; ++i) 
		sum += arr[i];
	return sum;
}
void test_sum() {
	int x0 = 28, x1 = 42, x2 = 101, res = 0;
	x0 = mksym_i32(); x1 = mksym_i32(); // x2 = mksym_i32();
	limit2_i32(&x0,28,42);
	limit2_i32(&x1,-13,-1);
	res = sum(x0,x1,x2);
	gen_sum(x0,x1,x2,res);
}


void gen_sum2(int *arr, int size, int res);
int sum2(int *arr, int size) {
	int sum = 0;
	for (int i = 0; i < size; i++)
		sum += arr[i];
	return sum;
}

void test_sum2() {
	int arr[5];
	for (int i = 0; i < 5; i++) {
		arr[i] = mksym_i32();
		limit2_i32(&arr[i],0,1);
	}
	int res = sum2(arr, 5);
	gen_sum2(arr, 5, res);
}






