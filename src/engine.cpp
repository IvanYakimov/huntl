#include "engine.hpp"

extern "C" {
	I32 binop_i32(Ref a, OpCode code, Flag flag, Ref b, I32 op1, Ref c, int32_t op2) {
		Dummy();
	}

	I32 icmp_i32(Ref res, Cond cond, Ref op1, I32 v1, Ref op2, I32 v2) {
		Dummy();
	}

	I32 alloca_i32(Ref res, I32 allocator) {

	}
}

int32_t Dummy() {
	std::cout << "handler catched\n";
}
