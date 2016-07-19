#ifndef __BUILT_IN_HPP__
#define __BUILT_IN_HPP__

#include "llvm/IR/InstVisitor.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "holder.hpp"
#include "context.hpp"

#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>

#include <functional>

namespace interpreter {
	using BuiltIn = std::function<memory::HolderPtr(llvm::Function*, memory::ArgMapPtr)>;
	using BuiltInPtr = std::shared_ptr<BuiltIn>;
	using BuiltInMap = std::map<llvm::Function*, BuiltIn>;

	class MkSym {
	public:
		MkSym(ContextRef context_, unsigned size);
		memory::HolderPtr operator()(llvm::Function* f, memory::ArgMapPtr args);
	private:
		ContextRef context_;
		const unsigned size_;
	};

	class Gen {
	public:
		Gen(ContextRef context, llvm::Function* target, llvm::Module* module);
		memory::HolderPtr operator()(llvm::Function* f, memory::ArgMapPtr args);
	private:
		ContextRef context_;
		llvm::Function* target_;
		llvm::Module* module_;
	};
}

#endif
