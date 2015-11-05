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

class IRegisterMap
{
public:
	virtual ~IRegisterMap () = 0;
	virtual void Add (const llvm::Instruction *inst) = 0;
};

class PatternMatcher : public llvm::InstVisitor <PatternMatcher>
{
public:
  PatternMatcher () {}

  //TODO: check, whether of not these methods should be private
private:
  void visitAllocaInst (const llvm::AllocaInst &inst);
  void visitLoadInst (const llvm::LoadInst &inst);
  void visitStoreInst (const llvm::StoreInst &inst);

protected:
  std::unique_ptr <IRegisterMap> register_map_;

private:
  // "pattern matching"
  bool Case (const llvm::Instruction &inst, unsigned i); // base case
  template <typename T, typename... Targs>
  bool Case (const llvm::Instruction &inst, unsigned i, T value, Targs... Fargs); // inductive case
};

# endif /* __INST_PRINTER_HPP__ */
