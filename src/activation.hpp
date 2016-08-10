#ifndef __ACTIVATION_HPP__
#define __ACTIVATION_HPP__

#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstVisitor.h"

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
	using ArgMap = std::map<RegisterName, memory::HolderPtr>;
	using ArgMapPtr = std::shared_ptr<ArgMap>;
	class Activation {
	public:
		NONCOPYABLE(Activation);
		Activation(RamRef ram);
		~Activation();
		static ActivationPtr Create(RamRef ram);
		memory::HolderPtr GetArg(RegisterName address);
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
		//memory::RamAddress Alloca(HolderPtr initial);
		memory::RamAddress Alloca(const llvm::Type* allocated);
		HolderPtr Load(RegisterName address);
		// get location (with lazy allocation)
		RamAddress GetLocation(RegisterName variable);
		void Store(RegisterName address, HolderPtr holder);
		void Print();
	private:
		//memory::LocalMemoryPtr local_memory_;
		memory::RamAddress TryToAllocate(const llvm::Value* variable);
		std::map<RegisterName, RamAddress> local_display_;
		memory::RamRef ram_;
	};
}

#endif













