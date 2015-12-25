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
class ExprTest : public ::testing::Test {
public:
	std::shared_ptr<solver::Variable> MakeVar(std::string name) {
		return std::make_shared<solver::Variable>(name);
	}
};
}

TEST_F(ExprTest, Variable_ToString) {
	solver::Variable v("x");
	EXPECT_EQ("x", v.ToString());
}

TEST_F(ExprTest, Constant_ToString) {
	solver::ConstantI32 c(28);
	EXPECT_EQ("28", c.ToString());
}

TEST_F(ExprTest, BinryOp_GetOpCode) {
	solver::BinaryOperation op(NULL, NULL, solver::BinaryOperation::ADD);
	EXPECT_EQ(solver::BinaryOperation::ADD, op.GetOpCode());
}

TEST_F(ExprTest, BinaryOp_GetOpCodeName) {
	solver::BinaryOperation op(NULL, NULL, solver::BinaryOperation::ADD);
	EXPECT_EQ("add", op.GetOpCodeName());
}

TEST_F(ExprTest, BinaryOp_ToString) {
	auto l = MakeVar("x");
	auto r = MakeVar("y");
	solver::BinaryOperation add(l, r, solver::BinaryOperation::OpCode::ADD);
	EXPECT_EQ("add x y", add.ToString());
}
