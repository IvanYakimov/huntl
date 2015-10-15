# ifndef __FUNC_PRINTER_HPP__
# define __FUNC_PRINTER_HPP__

// based on http://llvm.org/docs/WritingAnLLVMPass.html tutorial

// USEFUL REFERENCES:
// * learn llvm by example
// https://gist.github.com/alloy/d86b007b1b14607a112f
// * Analyse llvm code
// http://www.cs.cmu.edu/afs/cs.cmu.edu/academic/class/15745-s13/public/lectures/L6-LLVM-Detail-1up.pdf

# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/IR/Instruction.h"
# include "llvm/IR/InstIterator.h"
# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"

# include <set>

using namespace llvm;

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
				    false /* Only looks at CFG */,
				    false /* Analysis Pass */);

// TODO: add mapping for temporary "registy names" like %1, %2, ...
// http://llvm.org/docs/FAQ.html#what-api-do-i-use-to-store-a-value-to-one-of-the-virtual-registers-in-llvm-ir-s-ssa-representation

// TODO: check traversing order
// http://stackoverflow.com/questions/32853884/how-does-the-llvm-instvisitor-traverse-ir

# endif /* __FUNC_PRINTER_HPP__ */
