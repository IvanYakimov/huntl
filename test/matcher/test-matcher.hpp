#include "gtest/gtest.h"
#include "../../src/interpreter/matcher.hpp"

namespace {
	struct TestPass : public llvm::FunctionPass {
		static char ID;
		TestPass() : FunctionPass(ID) {}
		bool runOnFunction (llvm::Function &F) override;
	};
}

char TestPass::ID = 0;

static llvm::RegisterPass<TestPass> X("test", "test",
		false,
		false);
