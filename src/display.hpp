#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include "holder.hpp"

#include <map>
#include <cassert>
#include "creatable.hpp"

namespace memory {
	class Display;
	using DisplayPtr = std::shared_ptr<Display>;
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
		static DisplayPtr Create();
		void Print();
	private:
		using Pointer = std::pair<Address, HolderPtr>;
		using MemoryMap = std::map<Address, HolderPtr>;
		MemoryMap mmap_;
	};
}

#endif












