#ifndef __ACTIVATION_HPP__
#define __ACTIVATION_HPP__

#include "llvm/IR/Instruction.h"

#include <memory>
#include <cassert>
#include <map>

#include "object.hpp"
#include "creatable.hpp"
#include "holder.hpp"

namespace memory {
	class Activation;
	using ActivationPtr = std::shared_ptr<Activation>;
	class Activation {
	public:
		using Address = const llvm::Value*;
		NONCOPYABLE(Activation);
		Activation();
		~Activation();
		static ActivationPtr Create();
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













