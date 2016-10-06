#include <stdint.h>
#include <stdio.h>

extern int mksym_i32(void);
extern void add_arg_i32(int arg);
extern void add_res_i32(int res);
extern void generate_solution(void);

int main() {
	int a = mksym_i32(),
		b = mksym_i32();
	int res = 0;
	a += 28;
	if (a < b)
		res = a;
	else
		res = b;
	add_arg_i32(a);
	add_arg_i32(b);
	add_res_i32(res);
	generate_solution();
}
