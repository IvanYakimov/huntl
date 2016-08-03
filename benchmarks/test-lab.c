// see http://stackoverflow.com/questions/27447865/understanding-the-simplest-llvm-ir

void test_3() {
	int x = 99;
	int *y = &x;
	*y = 28;
	int result = x;
}

void test_4() {
	int x = 42;
	int y = x;
}
