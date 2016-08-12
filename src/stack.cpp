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

	Stack::MemoryCell::MemoryCell(HolderPtr holder, const Type* type, Alignment align) : type_(type) {
		assert (holder != nullptr and type != nullptr and align > 0);
		holder_ = holder;
		align_ = align;
	}

	Stack::MemoryCell::~MemoryCell() {

	}

	/*
	RamAddress Stack::Alloca(const Type* allocated) {
		if (allocated->isIntegerTy()) {
			const IntegerType* int_ty = llvm::dyn_cast<IntegerType>(allocated);
			auto width = int_ty->getBitWidth();
			auto val = 1;
			auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0);
			return Alloca(holder, memory::kDefAlign);
		}
		else if (allocated->isPointerTy()) {
			auto width = memory::kWordSize;
			//std::cerr << "allocate pointer" << std::endl;
			auto val = 1;
			auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0);
			return Alloca(holder, memory::kDefAlign);
		}
		else if (allocated->isArrayTy()) {
			const ArrayType* array_ty = llvm::dyn_cast<ArrayType>(allocated);
			const Type* el_ty = array_ty->getArrayElementType();
			auto len = array_ty->getArrayNumElements();
			auto first_el_addr = Alloca(el_ty);
			for (int i = 1; i < len; i++)
				Alloca(el_ty);
			return first_el_addr;
		}
		else
			assert (! "not implemented");
	}
	*/

	RamAddress Stack::Alloca(const Type* allocated) {
		if (allocated->isIntegerTy()) {
			const IntegerType* int_ty = llvm::dyn_cast<IntegerType>(allocated);
			auto width = int_ty->getBitWidth();
			auto val = 1;
			auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0 or width == 1);
			return Alloca(holder, allocated, memory::kDefAlign /*width / 8*/);
		}
		else if (allocated->isPointerTy()) {
			auto width = memory::kWordSize;
			auto val = 1;
			auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0);
			return Alloca(holder, allocated, memory::kDefAlign /*width / 8*/);
		}
		else if (allocated->isArrayTy()) {
			const ArrayType* array_ty = llvm::dyn_cast<ArrayType>(allocated);
			const Type* el_ty = array_ty->getArrayElementType();
			auto len = array_ty->getArrayNumElements();
			auto first_el_addr = Alloca(el_ty);
			for (int i = 1; i < len; i++)
				Alloca(el_ty);
			return first_el_addr;
		}
		else
			assert (! "not implemented");
	}

	RamAddress Stack::Alloca(HolderPtr holder, const llvm::Type* type, Alignment align) {
		auto addr = segment_stack_.top();
		segment_stack_.top() += align;
		MemoryCellPtr mcell = std::unique_ptr<MemoryCell>(new MemoryCell(holder, type, align));
		ram_.emplace(addr, std::move(mcell));
		//std::cerr << "alloca " << *holder << " to addr: " << addr << "\n";
		return addr;
	}

	void Stack::Write(HolderPtr holder, RamAddress addr, Alignment align) {
		//std::cerr << "write " << *holder << " to addr: " << addr << "\n";
		assert (addr < segment_stack_.top());
		auto it = ram_.find(addr);
		assert (it != ram_.end());
		assert (it->second->align_ == align);
		it->second->holder_ = holder;
	}

	HolderPtr Stack::Read(RamAddress addr, Alignment align) {
		//std::cerr << "read from addr: " << addr << "\n";
		assert (addr < segment_stack_.top());
		auto it = ram_.find(addr);
		assert (it != ram_.end());
		assert (it->second->align_ == align);
		auto res = it->second->holder_;
		assert (res != nullptr);
		return res;
	}

	const llvm::Type* Stack::GetType(RamAddress addr) {
		assert (addr < segment_stack_.top());
		auto it = ram_.find(addr);
		assert (it != ram_.end());
		auto res = it->second->type_;
		assert (res != nullptr);
		return res;
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






