# ifndef __PARSER_HPP__
# define __PARSER_HPP__

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
  struct Parser : public FunctionPass
  {
    static char ID;
    Parser() : FunctionPass (ID) {}
    bool runOnFunction (Function &F) override;
  };
}

char Parser::ID = 0;
static RegisterPass <Parser> X("Parser", "Parser pass",
				    false, // Only looks at CFG
				    false); // Analysis Pass

# endif /* __PARSER_HPP__ */









