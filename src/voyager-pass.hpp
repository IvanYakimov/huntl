# ifndef __VOYAGER_PASS_HPP__
# define __VOYAGER_PASS_HPP__

// LLVM
# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/Support/raw_ostream.h"

// STL
#include <iostream>

// Project
#include "kernel.hpp"

namespace
{
  struct VoyagerPass : public llvm::ModulePass
  {
    static char ID;
    VoyagerPass() : ModulePass (ID) {}
    //bool runOnFunction(llvm::Function &F) override;
    bool runOnModule(llvm::Module &M) override;
  };
}


char VoyagerPass::ID = 0;
static llvm::RegisterPass <VoyagerPass> X("ll-voyager", "ll-voyager virtual machine",
				    false, // Only looks at CFG
				    false); // Analysis Pass

# endif /* __PARSER_HPP__ */










