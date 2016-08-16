#ifndef __STACK_HPP__
#define __STACK_HPP__

#include "holder.hpp"
#include "creatable.hpp"
#include <map>
#include <stack>
#include <memory>
#include <iostream>

#include "ram-delc.hpp"
//#include "ram.hpp"
#include "meta-int.hpp"

#include "llvm/IR/Type.h"

namespace memory {
	class Stack;
	using StackRef = Stack&;
	class Stack {
		class ObjectRecord {
		public:
			ObjectRecord(RamAddress base, const llvm::Type* type);
			~ObjectRecord();
			RamAddress base_;
			const llvm::Type* object_type_;
		};
		using ObjectRecordPtr = std::shared_ptr<ObjectRecord>;
		class MemoryCell {
		public:
			MemoryCell(HolderPtr holder, const llvm::Type* type, Alignment align, ObjectRecordPtr bounds);
			~MemoryCell();
			Alignment align_;
			HolderPtr holder_;
			const llvm::Type* type_;
			ObjectRecordPtr bounds_;
		};
		using MemoryCellPtr = std::shared_ptr<MemoryCell>;
		std::stack<RamAddress> segment_stack_;
		std::map<RamAddress, MemoryCellPtr> ram_;
	public:
		Stack();
		~Stack();
		RamAddress Alloca(const llvm::Type* type, ObjectRecordPtr bounds = nullptr);
		void Write(HolderPtr holder, RamAddress addr);
		HolderPtr Read(RamAddress addr);
		const llvm::Type* GetType(RamAddress addr);
		const llvm::Type* GetMetaType(RamAddress addr);
		RamAddress GetBaseAddress(RamAddress addr);
		void Push();
		void Pop();
		unsigned long UpperBound();
		void Print();
	private:
		RamAddress AllocaScalar(auto width, const llvm::Type* allocated, ObjectRecordPtr bounds);
		RamAddress Alloca(HolderPtr holder, const llvm::Type* type, Alignment align, ObjectRecordPtr bounds);
		MemoryCellPtr GetMemoryCell(RamAddress addr);
	};
};

#endif /* __RAM_HPP__ */
