// useful links:
// https://github.com/google/googletest/blob/master/googletest/docs/Primer.mdy

// Project
# include "../../src/solver/expr.hpp"
# include "../../src/utils/object.hpp"

// Google Test
# include "gtest/gtest.h"

// STL
# include <memory>
# include <string>
# include <iostream>
# include <map>

using std::shared_ptr;

namespace solver {
class ExprTest : public ::testing::Test {
public:
	SharedExprPtr mkvar (std::string name) {
					return Variable::Create(name);
				};
	SharedExprPtr mkconst(std::int32_t value) {
		return ConstantI32::Create(value);
	}

	SharedExprPtr mkbinop(SharedExprPtr left, SharedExprPtr right, BinaryOperation::OpCode opcode) {
		return BinaryOperation::Create(left, right, opcode);
	}
};

//-------------------------------------------------------------------
// Variable

TEST_F(ExprTest, Variable_Accessors) {
	Variable v("x");
	EXPECT_EQ("x", v.ToString());
	EXPECT_EQ("x", v.GetName());
}

TEST_F(ExprTest, Variable_Comparison) {
	Variable x1("x"),
				x2("x"),
				x3("x"),
				y("y");
	EXPECT_EQ(x1, x1); // reflexivity
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x1); // symmetry
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x3); EXPECT_EQ(x1, x3); // transitivity
	EXPECT_NE(x1, y);
	EXPECT_NE(&x1, nullptr);
	EXPECT_NE(nullptr, &x1);
}

//-------------------------------------------------------------------
// Constant<T>

TEST_F(ExprTest, ConstantI32_Accessors) {
	std::int32_t val = 28,
			nval = -28;
	solver::ConstantI32 x(val),
			nx(nval);
	EXPECT_EQ(val, x.GetValue());
	EXPECT_EQ(nval, nx.GetValue());
	EXPECT_EQ("28", x.ToString());
	EXPECT_EQ("-28", nx.ToString());
}

TEST_F(ExprTest, ConstantI32_Comparison) {
	std::int32_t val1 = 28, val2 = 99;
	ConstantI32 x1(val1),
			x2(val1), x3(val1),
			y(val2);
	EXPECT_EQ(x1, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x3); EXPECT_EQ(x1, x3);
	EXPECT_NE(x1, y);
	EXPECT_NE(&x1, nullptr);
	EXPECT_NE(nullptr, &x1);
}

//-------------------------------------------------------------------
// BinaryOpration
TEST_F(ExprTest, BinOp_Accessors) {
	auto left = mkvar("x");
	auto right = mkvar("y");
	BinaryOperation bin_op(left, right, solver::BinaryOperation::ADD);

	EXPECT_EQ(left, bin_op.GetLeftChild());
	EXPECT_EQ(right, bin_op.GetRightChild());
	EXPECT_EQ(BinaryOperation::ADD, bin_op.GetOpCode());
	EXPECT_EQ("add x y", bin_op.ToString());
}

TEST_F(ExprTest, BinaryOp_Comparison_Basic) {
	BinaryOperation x1(nullptr, nullptr, BinaryOperation::ADD),
			x2(nullptr, nullptr, BinaryOperation::ADD),
			x3(nullptr, nullptr, BinaryOperation::ADD),
			y(nullptr, nullptr, BinaryOperation::SUB);
	EXPECT_EQ(x1, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x3); EXPECT_EQ(x1, x3);
	EXPECT_NE(x1, y);
	EXPECT_NE(&x1, nullptr);
	EXPECT_NE(nullptr, &x1);
}

//TODO all combinations
TEST_F(ExprTest, BinaryOp_Comparison_Deep) {
	auto x = mkvar ("x"),
			y = mkvar("y"),
			z = mkvar("z");
	BinaryOperation a(x, x, BinaryOperation::ADD),
			b(x, y, BinaryOperation::ADD),
			c(y, x, BinaryOperation::ADD),
			d(y, y, BinaryOperation::ADD);
	EXPECT_NE(a, b);
	EXPECT_NE(b, a);
	EXPECT_NE(c, d);
	EXPECT_NE(d, c);

}

TEST_F(ExprTest, BinaryOp_OpCodes) {
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
			{BinaryOperation::GREATER_THAN, "sgt"},
			{BinaryOperation::GREATER_OR_EQUAL, "sge"},
			{BinaryOperation::LESS_THAN, "slt"},
			{BinaryOperation::LESS_OR_EQUAL, "sle"}
	};

	for (it_type it = m.begin(); it != m.end(); it++) {
		solver::BinaryOperation op(NULL, NULL, it->first);
		EXPECT_EQ(it->second, op.GetOpCodeName());
	}
}

//-------------------------------------------------------------------
// SmartPointers and polymorphism testing
TEST_F(ExprTest, SmartPointer_Comparison_Variable) {
	auto x1 = mkvar("x"),
			x2 = mkvar("x"),
			x3 = mkvar("x"),
			y = mkvar("y");
	EXPECT_EQ(*x1, *x1);	// reflexivity
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
	EXPECT_NE(*x1, *y);
	EXPECT_NE(x1, nullptr);
	EXPECT_NE(nullptr, x1);
}

TEST_F(ExprTest, SmartPointer_Comparison_Constant) {
	std::int32_t val1 = 28, val2 = 99;
	auto x1 = mkconst(val1),
			x2 = mkconst(val1),
			x3 = mkconst(val1),
			y = mkconst(val2);
	EXPECT_EQ(*x1, *x1);	// reflexivity
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
	EXPECT_NE(*x1, *y);
	EXPECT_NE(x1, nullptr);
	EXPECT_NE(nullptr, x1);
}

TEST_F(ExprTest, SmartPointer_Comparison_BinaryOperation) {
	auto x1  = mkbinop(nullptr, nullptr, BinaryOperation::ADD),
			x2 = mkbinop(nullptr, nullptr, BinaryOperation::ADD),
			x3 = mkbinop(nullptr, nullptr, BinaryOperation::ADD),
			y = mkbinop(nullptr, nullptr, BinaryOperation::SUB);
	EXPECT_EQ(*x1, *x1);	// reflexivity
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
	EXPECT_NE(*x1, *y);
	EXPECT_NE(x1, nullptr);
	EXPECT_NE(nullptr, x1);
}

TEST_F(ExprTest, SmartPointer_Comparison_CrossTest) {
	auto var = mkvar("var");
	auto c1 = mkconst(28);
	auto c2 = mkconst(99);
	auto op = mkbinop(c1, c2, BinaryOperation::ADD);
	EXPECT_NE(*var, *c1);
	EXPECT_NE(*c1, *var);
	EXPECT_NE(*var, *op);
	EXPECT_NE(*op, *var);
	EXPECT_NE(*c1, *op);
	EXPECT_NE(*op, *c1);
}

}






