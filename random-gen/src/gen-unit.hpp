#ifndef __GEN_UNIT_HPP__
#define __GEN_UNIT_HPP__

# include "llvm/Support/raw_ostream.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Support/FileSystem.h"

#include <cassert>
#include <list>
#include <cstdlib>
#include <ctime>

#include <iostream>

#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

#include "gval-gen.hpp"

class GenUnit {
  //
public:
  void Run(llvm::Function &func);
};

#endif
