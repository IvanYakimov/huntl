# ifndef __EXECUTOR_HPP__
# define __EXECUTOR_HPP__

// LLVM
//# include "llvm/IR/Constants.h"

// Project
#include <exception>

#include "matcher.hpp"
//TODO: use -I option to perform headers search instead of ../ (?)

namespace interpreter {
	class InterpretationFailure final : public std::exception {
	public:
		InterpretationFailure(const llvm::Instruction &inst) {
			inst_ = std::unique_ptr<llvm::Instruction>(inst.clone());
		}

		virtual ~InterpretationFailure() {}

		virtual void Print() {
			llvm::errs() << "\nInterpretation failed on: " << *inst_ << "\n";
		}

	private:
		std::unique_ptr<llvm::Instruction> inst_ = NULL;
	};

	class Executor final : public Matcher
	{
	private:
		// Return
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst);
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const);
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val);
		virtual void HandleReturnInst (const llvm::Instruction &inst);

		// Branch
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump);

		// BinOp
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Cmp
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Alloca
		virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated);

		// Load
		virtual void HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr);

		// Store
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr);
	};
}

# endif /* __INTERPRETER_HPP__ */










