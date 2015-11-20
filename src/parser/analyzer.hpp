# ifndef __ANALYZER_HPP__
# define __ANALYZER_HPP__

// LLVM
# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/IR/Instruction.h"
# include "llvm/IR/InstIterator.h"
# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"
using namespace llvm;

// STL

// Project


namespace
{
  struct Analyzer : public FunctionPass
  {
    static char ID;
    Analyzer() : FunctionPass (ID) {}
    bool runOnFunction (Function &F) override;
  };
}

char Analyzer::ID = 0;
static RegisterPass <Analyzer> X("Analyzer", "Analyzer Pass",
				    false, // Only looks at CFG
				    false); // Analysis Pass

# endif /* __ANALYZER_HPP__ */










