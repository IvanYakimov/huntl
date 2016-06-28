#include "voyager-pass.hpp"

bool VoyagerPass::runOnFunction (llvm::Function &func) {
	interpreter::Kernel kernel;
	kernel.Do(func);
	//TODO: run interpreter on function
	// No transformations.
	return false;
}

