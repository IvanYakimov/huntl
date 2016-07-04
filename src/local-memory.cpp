#include "local-memory.hpp"

namespace memory {
	LocalMemory::LocalMemory() : mmap_() {

	}

	LocalMemory::~LocalMemory() {

	}

	void LocalMemory::Alloca(Address address, HolderPtr initial) {
		assert (mmap_.find(address) == mmap_.end());
		mmap_.emplace(address, initial);
	}

	HolderPtr LocalMemory::Load(Address address) {
		auto it = mmap_.find(address);
		assert (it != mmap_.end());
		return it->second;
	}

	void LocalMemory::Store(Address address, HolderPtr holder) {
		mmap_[address] = holder;
	}

	void LocalMemory::Print() {
		std::cout << "<-- Display:\n";
		for (auto it = mmap_.begin(); it != mmap_.end(); it++) {
			llvm::outs() << *(it->first) << " --> ";
			std::cout << *(it->second) << "\n";
		}
		std::cout << "--> \n";
	}

	LocalMemoryPtr LocalMemory::Create() {
		return utils::Create<LocalMemory>();
	}
}












