#include "voyager-pass.hpp"

bool VoyagerPass::runOnFunction (llvm::Function &func) {
	std::cerr << "hello" << std::endl;
	//TODO: run interpreter on function
	// No transformations.
	return false;
}

