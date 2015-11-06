# ifndef __PATTERN_MATCHER_HPP__
# define __PATTERN_MATCHER_HPP__


/* 
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
Licensed under LGPL license.
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

  void visitAllocaInst (const llvm::AllocaInst &inst);
  void visitLoadInst (const llvm::LoadInst &inst);
  void visitStoreInst (const llvm::StoreInst &inst);

protected:

  virtual void AddRegister (const llvm::Instruction &inst) = 0;

  virtual void HandleStoreInst (const llvm::Argument *arg, const llvm::AllocaInst *alloca) = 0;
  virtual void HandleStoreInst (const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca) = 0;
  virtual void HandleStoreInst (const llvm::Instruction &inst) = 0;

private:
  // "pattern matching"
  bool Case (const llvm::Instruction &inst, unsigned i); // base case
  template <typename T, typename... Targs>
  bool Case (const llvm::Instruction &inst, unsigned i, T value, Targs... Fargs); // inductive case
};

# endif /* __INST_PRINTER_HPP__ */
