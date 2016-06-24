#include "kernel.hpp"

namespace interpreter {
	using namespace llvm;

	void DebugFunctionInfo(const llvm::Function &func) {
	# ifdef DBG
		errs() << func.getName() << "\n";
	# endif
	}

	/** Run interpreter on function */
	void Kernel::Do(llvm::Function &func) {
		DebugFunctionInfo(func);
		std::cout << "hello" << std::endl;
		// Loop:
		// Check time, if it is done - select new state
		// Make step
		// 	- if step is forking - clone this state, update state table
		//	- else - back to start

		Evaluator executor;
		for (Function::iterator i = func.begin(), e = func.end(); i != e; ++i) {
			executor.visit(i);
		}
	}
}
