# ifndef __PATTERN_MATCHER_HPP__
# define __PATTERN_MATCHER_HPP__

/* 
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
*/

// useful links:
/*
http://en.cppreference.com/w/cpp/language/parameter_pack
http://www.cplusplus.com/reference/type_traits/remove_pointer/
 */

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"

# include <type_traits>
# include <map>
# include <string>
# include <memory>
# include <exception>
# include <ostream>

#include "../utils/interruption.hpp"
//# include "../utils/memory.hpp"

class MatchingFailure : public Interruption {
public:
	MatchingFailure(const llvm::Instruction &inst) {
		inst_ = std::unique_ptr<llvm::Instruction>(inst.clone());
	}
	virtual ~MatchingFailure() {/*nothing to free*/}

	void Print() {
		//TODO std::function<> instead of errs()
		llvm::errs() << "\nPattern Matching failed on: " << *inst_ << "\n";
	}
private:
	std::unique_ptr<llvm::Instruction> inst_ = NULL;
};

class PatternMatcher : public llvm::InstVisitor <PatternMatcher>
{
public:
  PatternMatcher () {}
  virtual ~PatternMatcher () {}

  // Specific Instruction type classes
  void visitReturnInst (const llvm::ReturnInst &inst);
  void visitBranchInst (const llvm::BranchInst &inst);
  // missed instructions
  void visitICmpInst (const llvm::ICmpInst &inst);
  // missed instructions
  void visitAllocaInst (const llvm::AllocaInst &inst);
  void visitLoadInst (const llvm::LoadInst &inst);
  void visitStoreInst (const llvm::StoreInst &inst);
  // missed instructions

protected:
  // Return
  virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val) = 0;
  virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) = 0;
  virtual void HandleReturnInst (const llvm::Instruction &inst) = 0;

  // Branch
  virtual void HandleBranchInst (const llvm::Instruction &inst,
		  const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) = 0;
  virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) = 0;

  // Cmp
  virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) = 0;

  // Alloca
  virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) = 0;

  // Load
  // TODO
  virtual void HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) = 0;

  // Store
  virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) = 0;
  virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) = 0;
  virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) = 0;

private:
  //TODO: extract a helper function
  // "pattern matching"
  bool Case (const llvm::Instruction &inst, unsigned i); // base case
  template <typename T, typename... Targs>
  bool Case (const llvm::Instruction &inst, unsigned i, T value, Targs... Fargs); // inductive case

  static inline void DebugInstInfo(const llvm::Instruction &inst);
  static inline void DebugOpList(const llvm::Instruction &inst);
};

# endif /* __INST_PRINTER_HPP__ */
