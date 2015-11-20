# ifndef __FUNC_PRINTER_HPP__
# define __FUNC_PRINTER_HPP__

// LLVM
# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/IR/Instruction.h"
# include "llvm/IR/InstIterator.h"
# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"
using namespace llvm;

// STL
# include <set>

// Project
#include "inst-printer.hpp"

namespace
{
  struct FuncPrinter : public FunctionPass
  {
    static char ID;
    FuncPrinter () : FunctionPass (ID) {}
    bool runOnFunction (Function &F) override;
  };
}

char FuncPrinter::ID = 0;
static RegisterPass <FuncPrinter> X("FuncPrinter", "Func Printer Pass",
				    false, // Only looks at CFG
				    false); // Analysis Pass

# endif /* __FUNC_PRINTER_HPP__ */
