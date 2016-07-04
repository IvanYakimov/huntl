#include "activation.hpp"

namespace memory {
	using memory::HolderPtr;

	Activation::Activation() : ret_(nullptr) {
	}

	Activation::~Activation() {

	}

	ActivationPtr Activation::Create() {
		return utils::Create<Activation>();
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
		auto res = arg_map_.find(address);
		assert (res != arg_map_.end());
		return res->second;
	}

	void Activation::SetArg(Address address, memory::HolderPtr value) {
		assert (llvm::isa<llvm::Argument>(address));
		assert (arg_map_.find(address) == arg_map_.end());
		arg_map_.emplace(address, value);
	}
}


















