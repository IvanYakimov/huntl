#include "activation.hpp"

#include "inst-matcher.tpp"

namespace memory {
	using memory::HolderPtr;
	using utils::Case;
	using utils::CaseHelper;

	Activation::Activation(RamRef ram) : RetVal(), PC(), ram_(ram) {
		//local_memory_ = memory::LocalMemory::Create();
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
		//assert (program_counter_ != nullptr);
		return program_counter_;
	}

	void Activation::ProgramCounter::Set(const llvm::BasicBlock* program_counter) {
		//assert (program_counter == nullptr);
		program_counter_ = program_counter;
	}

	memory::RamAddress Activation::Alloca(HolderPtr initial) {
		//local_memory_->Alloca(address, initial);
		//TODO: alignment
		auto addr = ram_.Stack().Alloca(initial, memory::Ram::def_align_);
		// note allocated value is not directly available (throw the display), but only from RAM address
		//local_display_.emplace(inst, addr);
		//assert (false);
		return addr;
	}

	HolderPtr Activation::Load(RegisterName register_name) {
		auto it = local_display_.find(register_name);
		assert (it != local_display_.end());
		auto addr = it->second;
		//TODO: align
		return ram_.Stack().Read(addr, memory::Ram::def_align_);
		//return local_memory_->Load(address);
	}

	void Activation::Store(RegisterName register_name, HolderPtr holder) {
		//local_memory_->Store(address, holder);
		auto it = local_display_.find(register_name);
		RamAddress addr;
		if (it == local_display_.end()) {
			addr = ram_.Stack().Alloca(holder, memory::Ram::def_align_);
			local_display_.emplace(register_name, addr);
		}
		else
			addr = it->second;
		ram_.Stack().Write(holder, addr, memory::Ram::def_align_);
	}

	memory::RamAddress Activation::TryToAllocate(const llvm::Value* variable) {
		// Get 'allocated' value
		llvm::Type* base_ty = variable->getType();
		unsigned width;


		if (base_ty->isIntegerTy()) {
			llvm::IntegerType* type = llvm::dyn_cast<llvm::IntegerType>(base_ty);
			width = type->getBitWidth();
		} // ret handled separately
		else if (base_ty->isPointerTy()) {
			width = memory::Ram::machine_word_bitsize_;
		}
		else if (llvm::isa<llvm::ReturnInst>(variable)) {
			auto ret = llvm::dyn_cast<llvm::ReturnInst>(variable);
			if (ret->getNumOperands() == 1) {
				auto operand = ret->getOperand(0);
				base_ty = operand->getType();
				llvm::IntegerType* type = llvm::dyn_cast<llvm::IntegerType>(base_ty);
				width = type->getBitWidth();
			}
		}
		else
			assert (! "unexpected behavior");

		interpreter::MetaInt val(width, 0);
		HolderPtr initial = memory::Concrete::Create(val);
		auto addr = ram_.Stack().Alloca(initial, memory::Ram::def_align_);
		local_display_.emplace(variable, addr);
		return addr;
	}

	RamAddress Activation::GetLocation(RegisterName variable) {
		auto it = local_display_.find(variable);
		RamAddress addr;
		if (it != local_display_.end())
			return it->second;
		else
			return TryToAllocate(variable);
	}

	void Activation::Print() {
		//local_memory_->Print();
	}
}


















