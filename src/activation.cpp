#include "activation.hpp"

namespace memory {
	using memory::HolderPtr;
#define DUMMY_ALLOCA 4

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

	void Activation::Alloca(RegisterName register_name, HolderPtr initial) {
		//local_memory_->Alloca(address, initial);
		//TODO: alignment
		auto addr = ram_.Stack().Alloca(initial, DUMMY_ALLOCA);
		memory_map_.emplace(register_name, addr);
	}

	HolderPtr Activation::Load(RegisterName register_name) {
		auto it = memory_map_.find(register_name);
		assert (it != memory_map_.end());
		auto addr = it->second;
		//TODO: align
		return ram_.Stack().Read(addr, DUMMY_ALLOCA);
		//return local_memory_->Load(address);
	}

	void Activation::Store(RegisterName register_name, HolderPtr holder) {
		//local_memory_->Store(address, holder);
		auto it = memory_map_.find(register_name);
		RamAddress addr;
		if (it == memory_map_.end()) {
			addr = ram_.Stack().Alloca(holder, DUMMY_ALLOCA);
			memory_map_.emplace(register_name, addr);
		}
		else
			addr = it->second;
		ram_.Stack().Write(holder, addr, DUMMY_ALLOCA);
	}

	RamAddress Activation::AddressOf(RegisterName target) {
		auto it = memory_map_.find(target);
		assert (it != memory_map_.end());
		return it->second;
	}

	void Activation::Print() {
		//local_memory_->Print();
	}
}


















