#ifndef __STACK_HPP__
#define __STACK_HPP__

#include "holder.hpp"
#include "creatable.hpp"
#include <map>
#include <stack>
#include <memory>

namespace memory {
	using Address = std::uint64_t;
	using Alignment = std::uint16_t;
	class Stack {
	public:
		Stack();
		~Stack();
		Address Alloca(HolderPtr holder, Alignment align);
		void Write(HolderPtr holder, Address addr, Alignment align);
		HolderPtr Read(Address addr, Alignment align);
		void Push();
		void Pop();
	private:
		class MemoryCell {
		public:
			MemoryCell(HolderPtr holder, Alignment align);
			~MemoryCell();
			Alignment align_;
			HolderPtr holder_;
		};
		using MemoryCellPtr = std::unique_ptr<MemoryCell>;
		std::stack<Address> segment_stack_;
		std::map<Address, MemoryCellPtr> ram_;
	};
};

#endif /* __RAM_HPP__ */
