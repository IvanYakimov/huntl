#ifndef __STACK_HPP__
#define __STACK_HPP__

#include "holder.hpp"
#include "creatable.hpp"
#include <map>
#include <stack>
#include <memory>

#include "ram-delc.hpp"
//#include "ram.hpp"

#include "llvm/IR/Type.h"

namespace memory {
	class Stack;
	using StackRef = Stack&;
	class Stack {
	public:
		Stack();
		~Stack();
		RamAddress Alloca(const llvm::Type* allocated);
		void Write(HolderPtr holder, RamAddress addr, Alignment align);
		HolderPtr Read(RamAddress addr, Alignment align);
		void Push();
		void Pop();
	private:
		RamAddress Alloca(HolderPtr holder, Alignment align);
		class MemoryCell {
		public:
			MemoryCell(HolderPtr holder, Alignment align);
			~MemoryCell();
			Alignment align_;
			HolderPtr holder_;
		};
		using MemoryCellPtr = std::unique_ptr<MemoryCell>;
		std::stack<RamAddress> segment_stack_;
		std::map<RamAddress, MemoryCellPtr> ram_;
	};
};

#endif /* __RAM_HPP__ */
