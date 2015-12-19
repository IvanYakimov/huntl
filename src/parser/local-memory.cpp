# include "local-memory.hpp"

using solver::SharedExprPtr;

void LocalMemory::Alloca() {
	//TODO
	//just do nothing?
}

void LocalMemory::Store(ConstInstPtr address, SharedExprPtr value) {
	memory_.insert(std::make_pair(address, value));
}

SharedExprPtr LocalMemory::Load(ConstInstPtr address) {
	return memory_[address];
}
