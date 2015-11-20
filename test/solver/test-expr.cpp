// useful links:
// https://github.com/google/googletest/blob/master/googletest/docs/Primer.mdy

// Project
# include "../../src/solver/expr.hpp"

// Google Test
# include "gtest/gtest.h"

// STL
# include <memory>
# include <string>
# include <iostream>

namespace {
class PrintExprTest : public ::testing::Test {
public:
	std::shared_ptr<solver::Variable> MakeVar(std::string name) {
		return std::make_shared<solver::Variable>(name);
	}
};
}

TEST_F(PrintExprTest, Variable) {
	solver::Variable v("x");
	//TODO: check operands order
	EXPECT_EQ("x", v.ToString());
}

TEST_F(PrintExprTest, Constant) {
	solver::ConstantI32 c(28);
	//TODO: check operands order
	EXPECT_EQ("28", c.ToString());
}

TEST_F(PrintExprTest, BinaryOp) {
	auto l = MakeVar("x");
	auto r = MakeVar("y");
	solver::BinaryOperation add(l, r, solver::BinaryOperation::OpCode::kAdd);
	//TODO: check operands order
	EXPECT_EQ("add x y", add.ToString());
}

int main (int argc, char *argv[]) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}
