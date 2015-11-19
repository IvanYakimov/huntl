// useful links:
// https://github.com/google/googletest/blob/master/googletest/docs/Primer.mdy

// Project
# include "../../src/solver/expr.hpp"

// Google Test
# include "gtest/gtest.h"

// STL
# include <memory>
using std::shared_ptr; using std::make_shared;

namespace {
class ExprTest : public ::testing::Test {

};
}

TEST_F(ExprTest, PrintVariable) {
	solver::Variable v("x");
	//TODO: check operands order
	EXPECT_EQ("x", v.ToString());
}

TEST_F(ExprTest, PrintConstant) {
	solver::ConstantI32 c(28);
	//TODO: check operands order
	EXPECT_EQ("28", c.ToString());
}

TEST_F(ExprTest, PrintAdd) {
	auto l = make_shared<solver::Variable>("x");
	auto r = make_shared<solver::Variable>("y");
	solver::BinaryOperation add(l, r, solver::BinaryOperation::OpCode::kAdd);
	//TODO: check operands order
	EXPECT_EQ("add x y", add.ToString());
}

int main (int argc, char *argv[]) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}

