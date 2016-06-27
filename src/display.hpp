#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include "llvm/IR/Instruction.h"

#include "holder.hpp"

#include <map>
#include <cassert>

namespace memory {
	/// Display stub
	class Display {
	public:
		NONCOPYABLE(Display);
		Display();
		~Display();
		using Address = const llvm::Value*;
		void Alloca(Address address, HolderPtr initial);
		HolderPtr Load(Address address);
		void Store(Address address, HolderPtr holder);
	private:
		using Pointer = std::pair<Address, HolderPtr>;
		using MemoryMap = std::map<Address, HolderPtr>;
		MemoryMap mmap_;
	};
}

#endif












