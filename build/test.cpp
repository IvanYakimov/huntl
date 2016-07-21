//#include "built-in.h"
#include <iostream>
#include <limits>

int main() {
	int x = -1;
	unsigned short y = (unsigned short)x;
	std::cout << "x = " << x << " y = " << y << std::endl;
}
