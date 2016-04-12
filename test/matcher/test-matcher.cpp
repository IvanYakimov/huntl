#include "test-matcher.hpp"

using namespace interpreter;
using namespace llvm;

bool TestPass::runOnFunction(Function &func) {
	errs() << "I'm a matcher test!\n";
	return false;
}

/*
class MatcherTest : public ::testing::Test {
};

TEST_F(MatcherTest, dummy) {

}
*/



