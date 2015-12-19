# ifndef __INTERPRETER_HPP__
# define __INTERPRETER_HPP__

// LLVM
//# include "llvm/IR/Constants.h"

// Project
# include "pattern-matcher.hpp"
# include "local-memory.hpp"
# include "../solver/expr.hpp"
# include "../solver/expr-factory.hpp"
# include "../utils/interruption.hpp"
//TODO: use -I option to perform headers search instead of ../
//# include "../solver/expr.hpp"

class InterpretationFailure final : public Interruption {
public:
	InterpretationFailure(const llvm::Instruction &inst) {
		inst_ = std::unique_ptr<llvm::Instruction>(inst.clone());
	}

	virtual ~InterpretationFailure() {/*nothing to do*/}

	virtual void Print() {
		llvm::errs() << "\nInterpretation failed on: " << *inst_ << "\n";
	}

private:
	std::unique_ptr<llvm::Instruction> inst_ = NULL;
};

class Interpreter final : public PatternMatcher
{
private:
	LocalMemory memory_;
	solver::ExprFactory expr_factory_;

	// Return
  virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val);
  virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst);
  virtual void HandleReturnInst (const llvm::Instruction &inst);

  // Branch
  virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
  virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump);

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

# endif /* __INTERPRETER_HPP__ */










