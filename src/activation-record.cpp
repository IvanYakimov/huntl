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
}

















