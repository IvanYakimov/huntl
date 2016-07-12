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


#include "evaluator.hpp"

namespace interpreter {
	class Kernel {
	public:
		Kernel();
		~Kernel();
		void Do(llvm::Function &func);
		void Do(llvm::Module &mod);
	private:
		Context context_;
		Evaluator eval_;
	};
}

#endif /*__INTERPRETER_HPP__*/
