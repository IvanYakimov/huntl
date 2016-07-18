#include "local-memory.hpp"

namespace memory {
	LocalMemory::LocalMemory() : mmap_() {

	}

	LocalMemory::~LocalMemory() {

	}

	void LocalMemory::Alloca(RegisterName address, HolderPtr initial) {
		assert (mmap_.find(address) == mmap_.end());
		mmap_.emplace(address, initial);
	}

	HolderPtr LocalMemory::Load(RegisterName address) {
		auto it = mmap_.find(address);
		assert (it != mmap_.end());
		return it->second;
	}

	void LocalMemory::Store(RegisterName address, HolderPtr holder) {
		mmap_[address] = holder;
	}

	void LocalMemory::Print() {
		std::cerr << "<-- Display:\n";
		for (auto it = mmap_.begin(); it != mmap_.end(); it++) {
			llvm::errs() << *(it->first) << " --> ";
			std::cerr << *(it->second) << "\n";
		}
		std::cerr << "--> \n";
	}

	LocalMemoryPtr LocalMemory::Create() {
		return utils::Create<LocalMemory>();
	}
}












