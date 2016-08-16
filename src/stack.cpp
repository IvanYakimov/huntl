#include "stack.hpp"

namespace memory {
	using llvm::Type; using llvm::IntegerType; using llvm::ArrayType;
	using interpreter::MetaInt;
	using llvm::Type;

	Stack::Stack() {
		segment_stack_.push(0);
	}

	Stack::~Stack() {
		assert (segment_stack_.top() == 0);
		segment_stack_.pop();
		assert (segment_stack_.size() == 0);
	}

	Stack::MemoryCell::MemoryCell(HolderPtr holder, const Type* type, Alignment align, ObjectRecordPtr bounds) : type_(type) {
		assert (holder != nullptr and type != nullptr and align > 0);
		holder_ = holder;
		align_ = align;
		bounds_ = bounds;
	}

	Stack::MemoryCell::~MemoryCell() {
		assert (holder_ != nullptr and type_ != nullptr and align_ > 0);
		assert (bounds_ != nullptr);
	}

	Stack::ObjectRecord::ObjectRecord(RamAddress base, const llvm::Type* type) {
		base_ = base;
		object_type_ = type;
	}
	Stack::ObjectRecord::~ObjectRecord() {
		assert (object_type_ != nullptr);
	}

	RamAddress Stack::AllocaScalar(auto width, const llvm::Type* allocated, ObjectRecordPtr bounds) {
		auto val = 1;
		auto holder = memory::Concrete::Create(MetaInt(width, val));
		RamAddress result;
		unsigned align = 0;
		if (width == 1)
			align = memory::kBoolAlign;
		else if (width % 8 == 0)
			align = width / 8;
		else
			assert (false);
		// if the scalar is not a part of another object
		if (bounds == nullptr) {
			RamAddress top = UpperBound();
			bounds = std::make_shared<ObjectRecord>(top, allocated);
			result = Alloca(holder, allocated, align, bounds);
			assert (top == result);
		}
		else {
			result = Alloca(holder, allocated, align, bounds);
		}
		return result;
	}

	RamAddress Stack::Alloca(const llvm::Type* allocated, ObjectRecordPtr bounds) {
		if (allocated->isIntegerTy()) {
			const IntegerType* int_ty = llvm::dyn_cast<IntegerType>(allocated);
			auto width = int_ty->getBitWidth();
			assert (width % 8 == 0 or width == 1);
			return AllocaScalar(width, allocated, bounds);
		}
		else if (allocated->isPointerTy()) {
			auto width = memory::kWordSize;
			//auto val = 1;
			//auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0);
			return AllocaScalar(width, allocated, bounds);
			//return Alloca(holder, allocated, memory::kDefAlign);
		}
		else if (allocated->isArrayTy()) {
			const ArrayType* array_ty = llvm::dyn_cast<ArrayType>(allocated);
			const Type* el_ty = array_ty->getArrayElementType();
			auto len = array_ty->getArrayNumElements();
			auto top = UpperBound();
			bounds = std::make_shared<ObjectRecord>(top, array_ty);
			auto first_el_addr = Alloca(el_ty, bounds);
			assert (first_el_addr == top);
			for (int i = 1; i < len; i++) {
				Alloca(el_ty, bounds);
			}
			return first_el_addr;
		}
		else
			assert (! "not implemented");
	}


	RamAddress Stack::Alloca(HolderPtr holder, const llvm::Type* type, Alignment align, ObjectRecordPtr bounds) {
		auto addr = segment_stack_.top();
		segment_stack_.top() += align;
		MemoryCellPtr mcell = std::make_shared<MemoryCell>(holder, type, align, bounds);
		ram_.emplace(addr, mcell);
		return addr;
	}

	Stack::MemoryCellPtr Stack::GetMemoryCell(RamAddress addr) {
		assert (addr < segment_stack_.top());
		auto it = ram_.find(addr);
		assert (it != ram_.end());
		auto res = it->second;
		assert (res != nullptr);
		return res;
	}

	void Stack::Write(HolderPtr holder, RamAddress addr) {
		auto mc = GetMemoryCell(addr);
		mc->holder_ = holder;
	}

	HolderPtr Stack::Read(RamAddress addr) {
		auto mc = GetMemoryCell(addr);
		auto res = mc->holder_;
		assert (res != nullptr);
		return res;
	}

	const llvm::Type* Stack::GetType(RamAddress addr) {
		auto mc = GetMemoryCell(addr);
		auto res = mc->type_;
		assert (res != nullptr);
		return res;
	}

	const llvm::Type* Stack::GetMetaType(RamAddress addr) {
		auto mc = GetMemoryCell(addr);
		return mc->bounds_->object_type_;
	}

	RamAddress Stack::GetBaseAddress(RamAddress addr) {
		auto mc = GetMemoryCell(addr);
		return mc->bounds_->base_;
	}

	void Stack::Push() {
		auto top_addr = segment_stack_.top();
		segment_stack_.push(top_addr);
	}

	void Stack::Pop() {
		segment_stack_.pop();
		auto top_addr = segment_stack_.top();
		for (auto it = ram_.begin(); it != ram_.end(); ) {
			if (it->first >= top_addr)
				it = ram_.erase(it);
			++it;
		}
	}

	void Stack::Print() {
		std::cerr << "Stack trace:\n";
		for (auto it = ram_.begin(); it != ram_.end(); ++it) {
			std::cerr << it->first << ", align " << it->second->align_ << " -> " << *it->second->holder_ << "\n";
		}
		std::cerr << "\n";
	}

	unsigned long Stack::UpperBound() {
		return segment_stack_.top();
	}
}






