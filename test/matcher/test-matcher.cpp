#include "test-matcher.hpp"

#include <llvm/Pass.h>
#include <llvm/PassManager.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRPrintingPasses.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include <algorithm>

using namespace interpreter;
using namespace llvm;

Module* makeLLVMModule();

bool TestPass::runOnFunction(Function &func) {
	errs() << "I'm a matcher test!\n";
	return false;
}

//TODO: instruction creation framework
Module* makeLLVMModule() {
 // Module Construction
 Module* mod = new Module("test.ll", getGlobalContext());
 mod->setDataLayout("0x208baf8");
 mod->setTargetTriple("x86_64-pc-linux-gnu");
 return mod;
}

//TODO: try to adopt google test framework
//see http://stackoverflow.com/questions/13513905/how-to-setup-googletest-as-a-shared-library-on-linux
/*
class MatcherTest : public ::testing::Test {
};

TEST_F(MatcherTest, dummy) {

}
*/










