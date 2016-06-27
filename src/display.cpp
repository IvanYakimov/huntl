#include "display.hpp"

namespace memory {
	Display::Display() : mmap_() {

	}

	Display::~Display() {

	}

	void Display::Alloca(Address address, HolderPtr initial) {
		assert (mmap_.find(address) == mmap_.end());
		mmap_.emplace(address, initial);
	}

	HolderPtr Display::Load(Address address) {
		auto it = mmap_.find(address);
		assert (it != mmap_.end());
		return it->second;
	}

	void Display::Store(Address address, HolderPtr holder) {
		auto it = mmap_.find(address);
		assert (it != mmap_.end());
		it->second = holder;
	}

	void Display::Print() {
		std::cout << "<--display:\n";
		for (auto it = mmap_.begin(); it != mmap_.end(); it++) {
			llvm::outs() << *(it->first) << " -> ";
			std::cout << *(it->second) << "\n";
		}
		std::cout << "-->\n";
	}
}












