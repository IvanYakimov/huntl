# ifndef __EVALUATOR_HPP__
# define __EVALUATOR_HPP__

// STL
#include <exception>
#include <string>
#include <regex>
#include <functional>
#include <list>

// fork support
#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>

#include "activation.hpp"
#include "local-memory.hpp"
#include "matcher.hpp"

// Uses
#include "meta-evaluator.hpp"
#include "meta-int.hpp"
#include "solver.hpp"
#include "context.hpp"

#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"

//TODO: use -I option to perform headers search instead of ../ (?)

namespace interpreter {
	class Evaluator final : public Matcher {
	public:

		Evaluator(interpreter::ContextRef context);
		~Evaluator();
		NONCOPYABLE(Evaluator);
		void ProcessModule(llvm::Module *m);
		memory::HolderPtr CallFunction(llvm::Function *func, memory::ArgMapPtr args);

	private:
		MetaEvaluator meta_eval_;
		interpreter::ContextRef context_;
		auto ProduceHolder(const llvm::ConstantInt* constant_int);
		void Trace(const llvm::Instruction& inst);
		using BuiltIn = std::function<memory::HolderPtr(llvm::Function*, memory::ArgMapPtr)>;
		using BuiltInPtr = std::shared_ptr<BuiltIn>;
		using BuiltInMap = std::map<llvm::Function*, BuiltIn>;
		BuiltInMap builtins_;
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

	private:
		// Return
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst);
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *ret_const);
		virtual void HandleReturnInst (const llvm::Instruction &inst);

		// Branch
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump);

		// BinOp
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Cmp
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Alloca
		virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated);

		// Load
		virtual void HandleLoadInst (const llvm::Instruction &inst, const llvm::Instruction *instruction);

		// Store
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::Value *ptr);

		virtual void HandleCallInst(const llvm::CallInst &inst);
};
}

# endif /* __INTERPRETER_HPP__ */













