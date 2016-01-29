# include "local-memory.hpp"

using solver::SharedExpr;

void LocalMemory::Alloca(ConstValPtr allocated) {
}

void LocalMemory::Store(ConstValPtr address, SharedExpr value) {
	memory_[address] = value;
}

SharedExpr LocalMemory::Load(ConstValPtr address) {
	return memory_[address];
}
