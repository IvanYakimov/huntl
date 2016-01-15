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
# include <map>

namespace solver {
	class ExprTest : public ::testing::Test {
	};

	//TODO eq relation for constanti32 & binaryoperation

# ifdef NODEF

	TEST_F(ExprTest, Variable_ToString) {
		solver::Variable v("x");
		EXPECT_EQ("x", v.ToString());
	}

	TEST_F(ExprTest, Variable_EQ_Reflexivity) {
		solver::Variable v("x");
		EXPECT_EQ(v, v);
	}

	TEST_F(ExprTest, Variable_EQ_Simmetric) {
		solver::Variable x1("x");
		solver::Variable x2("x");
		EXPECT_EQ(x1, x2);
		EXPECT_EQ(x2, x1);
	}

	TEST_F(ExprTest, Variable_EQ_Transitivity) {
		Variable x1("x"),
				x2("x"),
				x3("x");
		EXPECT_EQ(x1, x2);
		EXPECT_EQ(x2, x3);
		EXPECT_EQ(x1, x3);
	}

	TEST_F(ExprTest, Variable_NE) {
		Variable x("x");
		Variable y("y");
		EXPECT_NE(x, y);
	}

	TEST_F(ExprTest, Variable_NE_NullPtr) {
		Variable *x = new Variable("x");
		EXPECT_NE(nullptr, x);
		delete x;
	}

# endif

# ifdef NODEF_2
TEST_F(ExprTest, Constant_ToString) {
	solver::ConstantI32 c(28);
	EXPECT_EQ("28", c.ToString());
}

TEST_F(ExprTest, BinryOp_GetOpCode) {
	// single test is enough
	solver::BinaryOperation op(NULL, NULL, solver::BinaryOperation::ADD);
	EXPECT_EQ(solver::BinaryOperation::ADD, op.GetOpCode());
}

TEST_F(ExprTest, BinaryOp_GetChildren) {
	auto left = MakeVar("x");
	auto right = MakeVar("y");
	BinaryOperation bin_op(left, right, solver::BinaryOperation::ADD);
	EXPECT_EQ(left, bin_op.GetLeftChild());
	EXPECT_EQ(right, bin_op.GetRightChild());
}

TEST_F(ExprTest, BinaryOp_GetOpCodeName) {
	typedef std::map <BinaryOperation::OpCode, std::string> map_type;
	typedef map_type::iterator it_type;

	map_type m = {
			/* arithmetical */
			{BinaryOperation::ADD, "add"},
			{BinaryOperation::SUB, "sub"},
			{BinaryOperation::MUL, "mul"},
			{BinaryOperation::SHIFT_LEFT, "shl"},
			{BinaryOperation::LOGICAL_SHIFT_RIGHT, "lshr"},
			{BinaryOperation::ARIRH_SHIFT_RIGHT, "ashr"},

			/* logical */
			{BinaryOperation::AND, "and"},
			{BinaryOperation::OR, "or"},
			{BinaryOperation::XOR, "xor"},

			/* Comparisons */
			{BinaryOperation::EQUAL, "eq"},
			{BinaryOperation::NOT_EQUAL, "ne"},
			{BinaryOperation::UNSIGNED_GREATER_THAN, "ugt"},
			{BinaryOperation::UNSIGNED_GREATER_OR_EQUAL, "uge"},
			{BinaryOperation::UNSIGNED_LESS_THAN, "ult"},
			{BinaryOperation::UNSIGNED_LESS_OR_EQUAL, "ule"},
			{BinaryOperation::SIGNED_GREATER_THAN, "sgt"},
			{BinaryOperation::SIGNED_GREATER_OR_EQUAL, "sge"},
			{BinaryOperation::SIGNED_LESS_THAN, "slt"},
			{BinaryOperation::SIGNED_LESS_OR_EQUAL, "sle"}
	};

	for (it_type it = m.begin(); it != m.end(); it++) {
		solver::BinaryOperation op(NULL, NULL, it->first);
		EXPECT_EQ(it->second, op.GetOpCodeName());
	}
}

TEST_F(ExprTest, BinaryOp_ToString) {
	auto l = MakeVar("x");
	auto r = MakeVar("y");
	solver::BinaryOperation add(l, r, solver::BinaryOperation::OpCode::ADD);
	EXPECT_EQ("add x y", add.ToString());
}

# endif

}
