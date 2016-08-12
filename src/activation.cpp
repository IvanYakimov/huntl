#include "activation.hpp"

#include "inst-matcher.tpp"

namespace memory {
	using memory::HolderPtr;
	using utils::Case;
	using utils::CaseHelper;
	using llvm::Type; using llvm::ArrayType; using llvm::IntegerType; using llvm::PointerType;
	using interpreter::MetaInt;

	Activation::Activation(RamRef ram) : RetVal(), PC(), ram_(ram) {
	}

	Activation::~Activation() {}

	ActivationPtr Activation::Create(RamRef ram) {
		return utils::Create<Activation>(ram);
	}

	memory::HolderPtr Activation::ReturnValue::Get() {
		assert (ret_ != nullptr);
		return ret_;
	}

	void Activation::ReturnValue::Set(memory::HolderPtr ret) {
		assert (ret_ == nullptr);
		ret_ = ret;
	}

	const llvm::BasicBlock* Activation::ProgramCounter::Get() {
		return program_counter_;
	}

	void Activation::ProgramCounter::Set(const llvm::BasicBlock* program_counter) {
		program_counter_ = program_counter;
	}

	RamAddress Activation::Alloca(const Type* allocated) {
		if (allocated->isIntegerTy()) {
			const IntegerType* int_ty = llvm::dyn_cast<IntegerType>(allocated);
			auto width = int_ty->getBitWidth();
			auto val = 1;
			auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0 or width == 1);
			return ram_.Stack().Alloca(holder, allocated, memory::kDefAlign /*width / 8*/);
		}
		else if (allocated->isPointerTy()) {
			auto width = memory::kWordSize;
			auto val = 1;
			auto holder = memory::Concrete::Create(MetaInt(width, val));
			assert (width % 8 == 0);
			return ram_.Stack().Alloca(holder, allocated, memory::kDefAlign /*width / 8*/);
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

	HolderPtr Activation::Load(RegisterName register_name) {
		auto it = local_display_.find(register_name);
		assert (it != local_display_.end());
		auto addr = it->second;
		return ram_.Stack().Read(addr, memory::Ram::def_align_);
	}

	void Activation::Store(RegisterName register_name, HolderPtr holder) {
		auto it = local_display_.find(register_name);
		RamAddress addr;
		if (it == local_display_.end()) {
			assert (! "lazy allocation is not expected for Store instruction");
		}
		else
			addr = it->second;
		ram_.Stack().Write(holder, addr, memory::Ram::def_align_);
	}

	memory::RamAddress Activation::LazyRegisterAllocation(const llvm::Value* variable) {
		llvm::Type* base_ty = variable->getType();
		RamAddress addr;

		if (base_ty->isIntegerTy()) {
			addr = Alloca(base_ty);
		}
		else if (base_ty->isPointerTy()) {
			addr = Alloca(base_ty);
		}
		else if (llvm::isa<llvm::ReturnInst>(variable)) {
			auto ret = llvm::dyn_cast<llvm::ReturnInst>(variable);
			if (ret->getNumOperands() == 1) {
				auto operand = ret->getOperand(0);
				auto ret_val_ty = operand->getType();
				addr = Alloca(ret_val_ty);
			}
			else
				assert (! "unexpected number of ret operands");
		}
		else
			assert (! "unexpected type for lazy allocation");

		local_display_.emplace(variable, addr);
		return addr;
	}

	RamAddress Activation::GetLocation(RegisterName variable) {
		auto it = local_display_.find(variable);
		RamAddress addr;
		if (it != local_display_.end())
			return it->second;
		else
			return LazyRegisterAllocation(variable);
	}

	void Activation::Print() {
		//local_memory_->Print();
	}
}


















