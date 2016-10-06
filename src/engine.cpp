#include "engine.hpp"

extern "C" {
	I32 binop_i32(Ref a, OpCode code, Flag flag, Ref b, I32 op1, Ref c, int32_t op2) {
		Dummy();
	}
}

int32_t Dummy() {
	std::cout << "add: \n";
}
