#ifndef __EXECUTION_DRIVER_HPP__
#define __EXECUTION_DRIVER_HPP__

// LLVM
//# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
//# include "llvm/IR/Instruction.h"
//# include "llvm/IR/InstIterator.h"
//# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"
//# include "llvm/Support/Debug.h"

// Project



#include "evaluator.hpp"

namespace interpreter {
	class Kernel {
	public:
		void Do(llvm::Function &func);
	};
}

#endif /*__INTERPRETER_HPP__*/
