# ifndef __INST_PRINTER_HPP__
# define __INST_PRINTER_HPP__

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

using namespace llvm;

struct PatternMatcher : public InstVisitor <PatternMatcher>
{
  PatternMatcher () {}
  // --------------------------------------------------
  // Specific Instruction type classes
  void visitReturnInst (const ReturnInst &inst);
  void visitBranchInst (const BranchInst &inst);
  void visitICmpInst (const ICmpInst &inst);  
  void visitAllocaInst (const AllocaInst &inst);
  void visitLoadInst (const LoadInst &inst);
  void visitStoreInst (const StoreInst &inst);
  void visitBinaryOperator (const BinaryOperator &inst);
  
  // --------------------------------------------------
private:
  void PrintOpList (const llvm::Instruction *inst);
  void PrintPrefix (const llvm::Instruction *inst);
  void PrintArgOp (const llvm::Argument *arg);
  void PrintAllocaOp (const llvm::AllocaInst *alloca);
  void PrintLoadOp (const llvm::LoadInst *load);
  void PrintBinaryOperatorOp (const llvm::BinaryOperator *bin_op);
  void PrintConstantIntOp (const llvm::ConstantInt *constant);


  // "pattern matching"
  bool Case (const Instruction &inst, unsigned i); // base case
  template <typename T, typename... Targs>
  bool Case (const Instruction &inst, unsigned i, T value, Targs... Fargs); // inductive case

  class RegisterMap
  {
  public:
    typedef unsigned RegisterNumber;
    void Add (const llvm::Instruction *inst);
    RegisterNumber GetNumber (const llvm::Instruction *inst);
    std::string GetName (const llvm::Instruction *inst);
  private:
    std::map <const llvm::Instruction*, RegisterNumber> map_;
    RegisterNumber counter_ = 0;
  } register_map_;
};

# endif /* __INST_PRINTER_HPP__ */
