#ifndef __INTERPRETER_HPP__
#define __INTERPRETER_HPP__

// LLVM
//# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
//# include "llvm/IR/Instruction.h"
//# include "llvm/IR/InstIterator.h"
//# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"
//# include "llvm/Support/Debug.h"

// Project
# include "executor.hpp"

namespace interpreter {
	class Interpreter {
		void Do(llvm::Function &func);
	};
}

#endif /*__INTERPRETER_HPP__*/
