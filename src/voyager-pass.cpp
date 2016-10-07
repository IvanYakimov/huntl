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


bool VoyagerPass::runOnModule(llvm::Module &M) {
	transform::Transform tr(M);
	tr.visit(M);
	llvm::errs().flush();
	llvm::errs() << M;
	return true;
	/*
	interpreter::Kernel kernel;
	kernel.Do(M);
	// No transformations
	return false;
	*/
}

