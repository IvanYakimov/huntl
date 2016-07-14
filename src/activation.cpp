#include "activation.hpp"

namespace memory {
	using memory::HolderPtr;

	Activation::Activation() : RetVal(), PC() {
		local_memory_ = memory::LocalMemory::Create();
	}

	Activation::~Activation() {}

	ActivationPtr Activation::Create() {
		return utils::Create<Activation>();
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

	void Activation::Alloca(Address address, HolderPtr initial) {
		local_memory_->Alloca(address, initial);
	}

	HolderPtr Activation::Load(Address address) {
		return local_memory_->Load(address);
	}

	void Activation::Store(Address address, HolderPtr holder) {
		local_memory_->Store(address, holder);
	}

	void Activation::Print() {
		local_memory_->Print();
	}
}


















