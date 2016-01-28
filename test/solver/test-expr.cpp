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
# include <list>
# include <tuple>
# include <functional>

using std::shared_ptr;

namespace solver {
class ExprTest : public ::testing::Test {
public:
	SharedExprPtr mkvar (std::string name) {
		return std::make_shared<Var>(name);
	}
	SharedExprPtr mkconst(std::int32_t value) {
		return std::make_shared<ConstI32>(value);
	}

	SharedExprPtr mkbinop(SharedExprPtr left, SharedExprPtr right, Kind opcode) {
		return std::make_shared<BinOp>(left, right, opcode);
	}
};

//-------------------------------------------------------------------
// Variable

TEST_F(ExprTest, Variable_Creation) {
	bool status = false;
	try {
		Var v(nullptr);
	}
	catch (std::exception e) {
		status = true;
	}
	ASSERT_TRUE(status);

	status = false;
	try {
		Var v("");
	}
	catch (std::exception e) {
		status = true;
	}
	ASSERT_TRUE(status);
}

TEST_F(ExprTest, Variable_Accessors) {
	Var v("x");
	EXPECT_EQ("x", v.ToString());
	EXPECT_EQ("x", v.GetName());
}

TEST_F(ExprTest, Variable_Comparison) {
	Var x1("x"),
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
	auto f = [] (std::int32_t val) {
		ConstI32 x(val);
		EXPECT_EQ(val, x.GetValue());
		EXPECT_EQ(std::to_string(val), x.ToString());
	};

	std::list<std::int32_t> val_list = {
			0,
			42,
			214,
			-42,
			INT32_MIN,
			INT32_MAX
	};

	for_each(val_list.begin(), val_list.end(), f);
}

TEST_F(ExprTest, ConstantI32_Comparison) {
	std::int32_t val1 = 28, val2 = 99;
	ConstI32 x1(val1),
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
	BinOp bin_op(left, right, solver::Kind::ADD);

	EXPECT_EQ(left, bin_op.GetLeftChild());
	EXPECT_EQ(right, bin_op.GetRightChild());
	EXPECT_EQ(Kind::ADD, bin_op.GetKind());
	EXPECT_EQ("add x y", bin_op.ToString());
}

TEST_F(ExprTest, BinaryOp_Comparison_Basic) {
	BinOp x1(nullptr, nullptr, Kind::ADD),
			x2(nullptr, nullptr, Kind::ADD),
			x3(nullptr, nullptr, Kind::ADD),
			y(nullptr, nullptr, Kind::SUB);
	EXPECT_EQ(x1, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x3); EXPECT_EQ(x1, x3);
	EXPECT_NE(x1, y);
	EXPECT_NE(&x1, nullptr);
	EXPECT_NE(nullptr, &x1);
}

//TODO all combinations (how one can do it?)
TEST_F(ExprTest, BinaryOp_Comparison_Deep) {
	auto x = mkvar ("x"),
			y = mkvar("y"),
			z = mkvar("z");
	BinOp a(x, x, Kind::ADD),
			b(x, y, Kind::ADD),
			c(y, x, Kind::ADD),
			d(y, y, Kind::ADD);
	EXPECT_NE(a, b);
	EXPECT_NE(b, a);
	EXPECT_NE(c, d);
	EXPECT_NE(d, c);

}

TEST_F(ExprTest, Kind) {
	typedef std::map <Kind, std::string> map_type;
	typedef map_type::iterator it_type;

	map_type m = {
			/* arithmetical */
			{Kind::ADD, "add"},
			{Kind::SUB, "sub"},
			{Kind::MUL, "mul"},
			{Kind::SHL, "shl"},
			{Kind::LSHR, "lshr"},
			{Kind::ASHR, "ashr"},

			/* logical */
			{Kind::AND, "and"},
			{Kind::OR, "or"},
			{Kind::XOR, "xor"},

			/* Comparisons */
			{Kind::EQ, "eq"},
			{Kind::NE, "ne"},
			{Kind::UGE, "uge"},
			{Kind::UGT, "ugt"},
			{Kind::ULE, "ule"},
			{Kind::ULT, "ult"},
			{Kind::SGT, "sgt"},
			{Kind::SGE, "sge"},
			{Kind::SLT, "slt"},
			{Kind::SLE, "sle"}
	};

	for (it_type it = m.begin(); it != m.end(); it++) {
		solver::BinOp op(NULL, NULL, it->first);
		EXPECT_EQ(it->second, op.GetKindName());
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
	auto x1  = mkbinop(nullptr, nullptr, Kind::ADD),
			x2 = mkbinop(nullptr, nullptr, Kind::ADD),
			x3 = mkbinop(nullptr, nullptr, Kind::ADD),
			y = mkbinop(nullptr, nullptr, Kind::SUB);
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
	auto op = mkbinop(c1, c2, Kind::ADD);
	EXPECT_NE(*var, *c1);
	EXPECT_NE(*c1, *var);
	EXPECT_NE(*var, *op);
	EXPECT_NE(*op, *var);
	EXPECT_NE(*c1, *op);
	EXPECT_NE(*op, *c1);
}

//------------------------------------------------------------------
TEST_F(ExprTest, HelperOperators) {
	typedef std::function<SharedExprPtr(SharedExprPtr, SharedExprPtr)> oper;
	typedef std::tuple<Kind, oper> kind_to_op;
	using std::make_tuple;
	std::list<kind_to_op> l = {
			make_tuple(Kind::ADD, Add),
			make_tuple(Kind::SUB, Sub),
			make_tuple(Kind::MUL, Mul),
			make_tuple(Kind::SDIV, Sdiv),
			make_tuple(Kind::SREM, Srem),
			make_tuple(Kind::UDIV, Udiv),
			make_tuple(Kind::UREM, Urem),
			make_tuple(Kind::SHL, Shl),
			make_tuple(Kind::LSHR, Lshr),
			make_tuple(Kind::ASHR, Ashr),
			make_tuple(Kind::AND, And),
			make_tuple(Kind::OR, Or),
			make_tuple(Kind::XOR, Xor),
			make_tuple(Kind::EQ, Eq),
			make_tuple(Kind::NE, Ne),
			make_tuple(Kind::SGE, Sge),
			make_tuple(Kind::SGT, Sgt),
			make_tuple(Kind::SLE, Sle),
			make_tuple(Kind::SLT, Slt),
			make_tuple(Kind::UGE, Uge),
			make_tuple(Kind::UGT, Ugt),
			make_tuple(Kind::ULE, Ule),
			make_tuple(Kind::ULT, Ult)
	};

	auto checker = [] (kind_to_op t) {
		static auto l = V("l");
		static auto r = V("r");
		Kind kind = std::get<0>(t);
		oper op = std::get<1>(t);
		SharedExprPtr expr = op(l, r);
		auto binop = std::dynamic_pointer_cast<BinOp>(expr);
		ASSERT_EQ(binop->GetKind(), kind);
		ASSERT_EQ(binop->GetLeftChild(), l);
		ASSERT_EQ(binop->GetRightChild(), r);
	};

	std::for_each(l.begin(), l.end(), checker);
}

//-------------------------------------------------------------------
// Casting
TEST_F(ExprTest, Cast) {
	Expr *v = new Var("x"),
			*c = new ConstI32(28);
	auto p1 = dynamic_cast<ConstI32*>(v);
	auto p2 = dynamic_cast<Var*>(c);
	ASSERT_EQ(nullptr, p1);
	ASSERT_EQ(nullptr, p2);
}

TEST_F(ExprTest, PointerCast) {
	SharedExprPtr v = V("x"),
			c = C(28),
			b = Eq(v, c);

	auto pvv = std::dynamic_pointer_cast<Var>(v);
	auto pvc = std::dynamic_pointer_cast<ConstI32>(v);
	auto pvb = std::dynamic_pointer_cast<BinOp>(v);

	auto pcv = std::dynamic_pointer_cast<Var>(c);
	auto pcc = std::dynamic_pointer_cast<ConstI32>(c);
	auto pcb = std::dynamic_pointer_cast<BinOp>(c);

	auto pbv = std::dynamic_pointer_cast<Var>(b);
	auto pbc = std::dynamic_pointer_cast<ConstI32>(b);
	auto pbb = std::dynamic_pointer_cast<BinOp>(b);

	ASSERT_NE(nullptr, pvv);
	ASSERT_NE(nullptr, pcc);
	ASSERT_NE(nullptr, pbb);

	ASSERT_EQ(*v, *pvv);
	ASSERT_EQ(nullptr, pvc);
	ASSERT_EQ(nullptr, pvb);

	ASSERT_EQ(nullptr, pcv);
	ASSERT_EQ(*c, *pcc);
	ASSERT_EQ(nullptr, pcb);

	ASSERT_EQ(nullptr, pbv);
	ASSERT_EQ(nullptr, pbc);
	ASSERT_EQ(*b, *pbb);
}

}












