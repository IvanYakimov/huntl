#include "voyager-pass.hpp"

/*
bool VoyagerPass::runOnFunction (llvm::Function &func) {
	//interpreter::Kernel kernel;
	//kernel.Do(func);
	//TODO: run interpreter on function
	// No transformations.

	return false;
}
*/

//#define JIT_EXPERIMENT

void JITExperiment(llvm::Module &M) {
	char buff[] = "hello world";
	auto f = M.begin();
	llvm::ExecutionEngine* jit = llvm::EngineBuilder(&M).create();
	std::vector<llvm::GenericValue> jit_args;
	llvm::GenericValue jit_res;
	llvm::GenericValue a_val;
	a_val.IntVal = llvm::APInt(32,2);
	jit_args.push_back(llvm::GenericValue(buff));
	jit_res = jit->runFunction(f, jit_args);
	llvm::errs() << jit_res.IntVal << "\n";
}

bool VoyagerPass::runOnModule(llvm::Module &M) {

#ifdef JIT_EXPERIMENT
	JITExperiment(M);
#else
	interpreter::Kernel kernel;
	kernel.Do(M);
#endif
	// No transformations
	return false;
}

