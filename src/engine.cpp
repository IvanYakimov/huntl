#include "engine.hpp"

extern "C" {
	int32_t add(Ref x) {
		return Dummy(x);
	}
}

int32_t Dummy(Ref x) {
	std::cout << "add: " << x << std::endl;
	return 101;
}
