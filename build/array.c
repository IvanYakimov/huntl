void func(const char* format, ...);

typedef struct {
	int x;
	float y;
}point;

int main() {
	func("hello world", 2, 28);
	char arr[12][28];
	point p;
	return p.y;
}
