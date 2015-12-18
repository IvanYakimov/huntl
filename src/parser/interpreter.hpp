# ifndef __INTERPRETER_HPP__
# define __INTERPRETER_HPP__

// Project
# include "pattern-matcher.hpp"
//TODO: use -I option to perform headers search instead of ../
//# include "../solver/expr.hpp"

class Interpreter final : public PatternMatcher
{
private:
	// Return
  virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val);
  virtual void HandleReturnInst (const llvm::Instruction &inst);

  // Branch
  virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
  virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump);
  virtual void HandleBranchInst (const llvm::Instruction &inst);

  // Cmp
  virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);
  virtual void HandleICmpInst (const llvm::Instruction &inst);

  // Alloca
  virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated);
  virtual void HandleAllocaInst (const llvm::Instruction &inst);

  // Load
  virtual void HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr);
  virtual void HandleLoadInst (const llvm::Instruction &inst);

  // Store
  virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr);
  virtual void HandleStoreInst (const llvm::Instruction &inst);
};

# endif /* __INTERPRETER_HPP__ */










