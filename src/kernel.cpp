#include "kernel.hpp"

namespace interpreter {
	using namespace llvm;

	void DebugFunctionInfo(const llvm::Function &func) {
	# ifdef DBG
		errs() << func.getName() << "\n";
	# endif
	}

	Kernel::Kernel() : context_(), eval_(context_){

	}

	Kernel::~Kernel() {

	}

	void Kernel::Do(llvm::Module &mod) {
		errs() << "module pass\n";
		eval_.ProcessModule(&mod);

	}

	/** Run interpreter on function */
	void Kernel::Do(llvm::Function &func) {
		errs() << "function pass\n";
		DebugFunctionInfo(func);
		errs() << func.getName() << "\n";
		errs() << "arg size: " << func.arg_size() << "\n";
		;
		for (llvm::Function::arg_iterator i = func.arg_begin(), e = func.arg_end(); i != e; ++i)
			errs() << *i;
		errs() << "\n";
		//llvm::Function::ArgumentListType arg_list = func.getArgumentList();
		/*
		for (Function::ArgumentListType::iterator i = arg_list.begin(), e = arg_list.end(); i != e; ++i) {
			outs << "arg\n";
		}
		*/
		//func.getArgumentList();
		// Loop:
		// Check time, if it is done - select new state
		// Make step
		// 	- if step is forking - clone this state, update state table
		//	- else - back to start

		/*
		Evaluator evaluator;
		for (Function::iterator i = func.begin(), e = func.end(); i != e; ++i) {
			evaluator.visit(i);
		}
		*/
	}
}
