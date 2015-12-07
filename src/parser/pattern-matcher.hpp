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
# include <type_traits>

# include <map>
# include <string>
# include <memory>
# include <exception>

// TODO: throw exception on unimplemented virtual methods (or maybe only in the constructor)
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
  // : missed instructions

protected:
  virtual void AddRegister (const llvm::Instruction *inst) = 0;

  // Store instruction
  virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int) = 0;
  virtual void HandleAllocaInst (const llvm::Instruction &inst) = 0;

  virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::AllocaInst *alloca) = 0;
  virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::AllocaInst *alloca) = 0;
  virtual void HandleStoreInst (const llvm::Instruction &inst) = 0;

  // Return instruction
  virtual void HandleReturnInst (const llvm::Instruction &inst) = 0;

private:
  //TODO: extract a helper function
  // "pattern matching"
  bool Case (const llvm::Instruction &inst, unsigned i); // base case
  template <typename T, typename... Targs>
  bool Case (const llvm::Instruction &inst, unsigned i, T value, Targs... Fargs); // inductive case
};

# endif /* __INST_PRINTER_HPP__ */
