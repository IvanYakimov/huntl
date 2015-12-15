# include "parser.hpp"

void Parser::DebugFunctionInfo(const llvm::Function &func) {
# ifdef DBG
	errs() << func.getName() << "\n";
# endif
}

bool Parser::runOnFunction (Function &func) {
	DebugFunctionInfo(func);

	Interpreter interpreter;
	for (Function::iterator i = func.begin(), e = func.end(); i != e; ++i) {
		interpreter.visit(i);
	}

	// No transformations.
	return false;
}

