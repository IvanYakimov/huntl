#ifndef __ACTIVATION_HPP__
#define __ACTIVATION_HPP__

#include "llvm/IR/Instruction.h"

#include <memory>
#include <cassert>
#include <map>

#include "object.hpp"
#include "creatable.hpp"
#include "holder.hpp"
#include "local-memory.hpp"
#include "memory-map-interface.hpp"

namespace memory {
	class Activation;
	using ActivationPtr = std::shared_ptr<Activation>;
	//TODO: customize :(
	using ArgMap = std::map<Address, memory::HolderPtr>;
	//using ArgMapPtr = std::shared_ptr<ArgMap>;
	class Activation {
	public:
		NONCOPYABLE(Activation);
		Activation(ArgMap arg_map);
		~Activation();
		static ActivationPtr Create(ArgMap arg_map);
		memory::HolderPtr GetArg(Address address);
		void SetArg(Address, memory::HolderPtr value);
		memory::HolderPtr GetRet();
		void SetRet(memory::HolderPtr ret);
		void Alloca(Address address, HolderPtr initial);
		HolderPtr Load(Address address);
		void Store(Address address, HolderPtr holder);
		void Print();
		memory::LocalMemoryPtr GetLocalMemoryPtr();
	private:
		memory::LocalMemoryPtr local_memory_;
		ArgMap arg_map_;
		memory::HolderPtr ret_;
	};
}

#endif













