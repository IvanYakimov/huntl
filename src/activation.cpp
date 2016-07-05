#include "activation.hpp"

namespace memory {
	using memory::HolderPtr;

	Activation::Activation(ArgMapPtr arg_map) {
		assert (arg_map != nullptr);
		arg_map_ = arg_map;
		ret_ = nullptr;
		local_memory_ = memory::LocalMemory::Create();
	}

	Activation::~Activation() {

	}

	ActivationPtr Activation::Create(ArgMapPtr arg_map) {
		return utils::Create<Activation>(arg_map);
	}

	memory::HolderPtr Activation::GetRet() {
		assert (ret_ != nullptr);
		return ret_;
	}

	void Activation::SetRet(memory::HolderPtr ret) {
		assert (ret_ == nullptr);
		ret_ = ret;
	}

	memory::HolderPtr Activation::GetArg(Address address) {
		assert (llvm::isa<llvm::Argument>(address));
		auto res = arg_map_->find(address);
		assert (res != arg_map_->end());
		return res->second;
	}

	void Activation::SetArg(Address address, memory::HolderPtr value) {
		assert (llvm::isa<llvm::Argument>(address));
		assert (arg_map_->find(address) == arg_map_->end());
		arg_map_->emplace(address, value);
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

	memory::LocalMemoryPtr Activation::GetLocalMemoryPtr() {
		return local_memory_;
	}
}


















