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
#include "llvm/IR/BasicBlock.h"
#include "ram.hpp"

namespace memory {
	class Activation;
	using ActivationPtr = std::shared_ptr<Activation>;
	//TODO: customize :(
	using ArgMap = std::map<Address, memory::HolderPtr>;
	using ArgMapPtr = std::shared_ptr<ArgMap>;
	class Activation {
	public:
		NONCOPYABLE(Activation);
		Activation(RamRef ram);
		~Activation();
		static ActivationPtr Create(RamRef ram);
		memory::HolderPtr GetArg(Address address);
		class ReturnValue {
		public:
			void Set(memory::HolderPtr value);
			memory::HolderPtr Get();
		private:
			memory::HolderPtr ret_ = nullptr;
		} RetVal;
		class ProgramCounter {
		public:
			void Set(const llvm::BasicBlock* program_counter);
			const llvm::BasicBlock* Get();
		private:
			const llvm::BasicBlock* program_counter_ = nullptr;
		} PC;
		void Alloca(Address address, HolderPtr initial);
		HolderPtr Load(Address address);
		void Store(Address address, HolderPtr holder);
		void Print();
	private:
		memory::LocalMemoryPtr local_memory_;
		memory::RamRef ram_;
	};
}

#endif













