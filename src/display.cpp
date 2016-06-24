#include "display.hpp"

namespace memory {
	Display::Display() : mmap_() {

	}

	Display::~Display() {

	}

	void Display::Alloca(Address address) {
		auto holder = Undef::Create();
		assert (mmap_.find(address) == mmap_.end());
		mmap_.emplace(address, holder);
	}

	HolderPtr Display::Read(Address address) {
		auto it = mmap_.find(address);
		assert (it != mmap_.end());
		return it->second;
	}

	void Display::Write(Address address, HolderPtr holder) {
		auto it = mmap_.find(address);
		assert (it != mmap_.end());
		it->second = holder;
	}
}












