#include "activation-record.hpp"

namespace memory {
	using memory::HolderPtr;

	ActivationRecord::ActivationRecord() : ret_(nullptr) {
	}

	ActivationRecord::~ActivationRecord() {

	}

	ActivationRecordPtr ActivationRecord::Create() {
		return utils::Create<ActivationRecord>();
	}

	memory::HolderPtr ActivationRecord::GetRet() {
		assert (ret_ != nullptr);
		return ret_;
	}

	void ActivationRecord::SetRet(memory::HolderPtr ret) {
		assert (ret_ == nullptr);
		ret_ = ret;
	}

	memory::HolderPtr ActivationRecord::GetArg(Address address) {
		assert (llvm::isa<llvm::Argument>(address));
		auto res = arg_map_.find(address);
		assert (res != arg_map_.end());
		return res->second;
	}

	void ActivationRecord::SetArg(Address address, memory::HolderPtr value) {
		assert (llvm::isa<llvm::Argument>(address));
		assert (arg_map_.find(address) == arg_map_.end());
		arg_map_.emplace(address, value);
	}
}


















