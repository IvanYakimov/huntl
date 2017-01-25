#include "randgen-pass.hpp"

using namespace llvm;

bool RandGenPass::runOnFunction (llvm::Function &func) {
  // TODO:
  GenUnit gunit;
  auto name = func.getName();
  //  errs() << name << "\n";
  if (name == "strcmp") {
    gunit.Run(func);
  }
  
  // No transformations.
  return false;
}

