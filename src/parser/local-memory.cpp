# include "local-memory.hpp"

using solver::SharedExprPtr;

void LocalMemory::Alloca(ConstValPtr allocated) {
}

void LocalMemory::Store(ConstValPtr address, SharedExprPtr value) {
	memory_[address] = value;
}

SharedExprPtr LocalMemory::Load(ConstValPtr address) {
	return memory_[address];
}
