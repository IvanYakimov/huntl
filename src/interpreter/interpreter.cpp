#include "interpreter.hpp"

void Interpreter::DebugFunctionInfo(const llvm::Function &func) {
# ifdef DBG
	errs() << func.getName() << "\n";
# endif
}

bool Interpreter::runOnFunction (Function &func) {
	DebugFunctionInfo(func);

	// Loop:
	// Check time, if it is done - select new state
	// Make step
	// 	- if step is forking - clone this state, update state table
	//	- else - back to start

	Executor executor;
	for (Function::iterator i = func.begin(), e = func.end(); i != e; ++i) {
		executor.visit(i);
	}

	// No transformations.
	return false;
}

