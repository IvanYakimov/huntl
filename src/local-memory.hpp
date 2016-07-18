#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include "holder.hpp"

#include <map>
#include <cassert>
#include "creatable.hpp"
#include "memory-map-interface.hpp"

namespace memory {
	class LocalMemory;
	using LocalMemoryPtr = std::shared_ptr<LocalMemory>;
	class LocalMemory : public memory::MemoryMapInterface {
	public:
		NONCOPYABLE(LocalMemory);
		LocalMemory();
		~LocalMemory();
		//using Address = const llvm::Value*;
		void Alloca(RegisterName address, HolderPtr initial);
		HolderPtr Load(RegisterName address);
		void Store(RegisterName address, HolderPtr holder);
		static LocalMemoryPtr Create();
		void Print();
	private:
		using Pointer = std::pair<RegisterName, HolderPtr>;
		using MemoryMap = std::map<RegisterName, HolderPtr>;
		MemoryMap mmap_;
	};
}

#endif












