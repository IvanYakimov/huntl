// useful links:
// https://github.com/google/googletest/blob/master/googletest/docs/Primer.mdy

# include "../../src/solver/expr.hpp"
# include "gtest/gtest.h"

namespace {
class ExprTest : public ::testing::Test {

};
}

TEST_F(ExprTest, PrintVariable) {
	solver::Variable v("x");
	EXPECT_EQ("x", v.ToString());
}

int main (int argc, char *argv[]) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}

