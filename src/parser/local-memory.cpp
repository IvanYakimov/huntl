# include "local-memory.hpp"

using solver::SharedExprPtr;

void LocalMemory::Alloca(ConstValPtr allocated) {
	//TODO
	//just do nothing?
}

void LocalMemory::Store(ConstValPtr address, SharedExprPtr value) {
	//TODO
	memory_[address] = value;
}

SharedExprPtr LocalMemory::Load(ConstValPtr address) {
	//TODO
	return memory_[address];
}
