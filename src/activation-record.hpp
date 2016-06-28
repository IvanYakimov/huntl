#ifndef __ACTIVATION_RECORD_HPP__
#define __ACTIVATION_RECORD_HPP__

#include <memory>
#include <cassert>

#include "object.hpp"
#include "creatable.hpp"
#include "holder.hpp"

namespace memory {
	class ActivationRecord;
	using ActivationRecordPtr = std::shared_ptr<ActivationRecord>;
	class ActivationRecord {
	public:
		NONCOPYABLE(ActivationRecord);
		ActivationRecord();
		~ActivationRecord();
		static ActivationRecordPtr Create();
		memory::HolderPtr GetRet();
		void SetRet(memory::HolderPtr ret);
	private:
		memory::HolderPtr ret_;
	};
}

#endif
