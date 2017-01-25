# ifndef __RANDGEN_PASS_HPP__
# define __RANDGEN_PASS_HPP__

// LLVM
# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/Support/raw_ostream.h"

// STL
#include <iostream>

// Project
#include "gen-unit.hpp"

namespace {
  struct RandGenPass : public llvm::FunctionPass {
    static char ID;
    RandGenPass() : FunctionPass (ID) {}
    virtual bool runOnFunction(llvm::Function &func);
  };
}

char RandGenPass::ID = 0;
static llvm::RegisterPass <RandGenPass>X("rand-gen",
					 "Feedback-directed random test generator.",
					  false, // Only looks at CFG
					  false); // Analysis Pass
# endif










