#ifndef __ACTIVATION_RECORD_HPP__
#define __ACTIVATION_RECORD_HPP__

#include "llvm/IR/Instruction.h"

#include <memory>
#include <cassert>
#include <map>

#include "object.hpp"
#include "creatable.hpp"
#include "holder.hpp"

namespace memory {
	class ActivationRecord;
	using ActivationRecordPtr = std::shared_ptr<ActivationRecord>;
	class ActivationRecord {
	public:
		using Address = const llvm::Value*;
		NONCOPYABLE(ActivationRecord);
		ActivationRecord();
		~ActivationRecord();
		static ActivationRecordPtr Create();
		memory::HolderPtr GetArg(Address address);
		void SetArg(Address, memory::HolderPtr value);
		memory::HolderPtr GetRet();
		void SetRet(memory::HolderPtr ret);
	private:
		using ArgMap = std::map<Address, memory::HolderPtr>;
		ArgMap arg_map_;
		memory::HolderPtr ret_;
	};
}

#endif













