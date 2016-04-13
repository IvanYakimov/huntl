#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;

LLVMContext &context_ = getGlobalContext();
Module *module_;
IRBuilder<> builder_ (getGlobalContext());

void InitModule() {
	module_ = new Module("test", context_);
	FunctionType *func_ty = FunctionType::get(Type::getVoidTy(getGlobalContext()), false);
	Function *func = Function::Create(func_ty, Function::ExternalLinkage, "test", module_);
	BasicBlock *entry_ = BasicBlock::Create(getGlobalContext(), "entry", func);
	builder_.SetInsertPoint(entry_);
	errs() << verifyFunction(*func) << "\n";
	errs() << *func << "\n";
	delete module_;
}

int main(int argc, char** argv, char **env) {
	InitModule();
	return 0;
}











