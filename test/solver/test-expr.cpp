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
	catch (std::logic_error &e) {
		status = true;
	}
	ASSERT_TRUE(status);

	status = false;
	try {
		Var v("");
	}
	catch (std::logic_error &e) {
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
TEST_F(ExprTest, BinOp_Creation) {
	auto v = V("x");
	bool s1 = false,
			s2 = false,
			s3 = false,
			s4 = false;
	try {
		BinOp b(nullptr, v, Kind::ADD);
	}
	catch (std::logic_error &e) {
		s1 = true;
	}

	try {
		BinOp b(v, nullptr, Kind::ADD);
	}
	catch (std::logic_error &e) {
		s2 = true;
	}

	try {
		BinOp b(nullptr, nullptr, Kind::ADD);
	}
	catch (std::logic_error &e) {
		s3 = true;
	}

	try {
		BinOp b(v, v, Kind::ADD);
		s4 = true;
	}
	catch (std::logic_error &e) {
		s4 = false;
	}

	ASSERT_TRUE(s1);
	ASSERT_TRUE(s2);
	ASSERT_TRUE(s3);
	ASSERT_TRUE(s4);
}

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
	auto v = V("x");
	BinOp x1(v, v, Kind::ADD),
			x2(v, v, Kind::ADD),
			x3(v, v, Kind::ADD),
			y(v, v, Kind::SUB);
	EXPECT_EQ(x1, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x1);
	EXPECT_EQ(x1, x2); EXPECT_EQ(x2, x3); EXPECT_EQ(x1, x3);
	EXPECT_NE(x1, y);
	EXPECT_NE(&x1, nullptr);
	EXPECT_NE(nullptr, &x1);
}

TEST_F(ExprTest, BinaryOp_Comparison_Deep) {
	auto x = V("x"),
			y = V("y");

	BinOp 	a1(x, x, Kind::ADD),
			a2(x, x, Kind::ADD),
			b1(x, y, Kind::ADD),
			b2(x, y, Kind::ADD),
			c1(y, x, Kind::ADD),
			c2(y, x, Kind::ADD),
			d1(y, y, Kind::ADD),
			d2(y, y, Kind::ADD);

	typedef std::tuple<BinOp, BinOp, bool> test_data;
	using std::make_tuple;
	std::list<test_data> l = {
			make_tuple(a1, a2, true),
			make_tuple(a1, b1, false),
			make_tuple(a1, c1, false),
			make_tuple(a1, d1, false),
			make_tuple(b1, b2, true),
			make_tuple(b1, c1, false),
			make_tuple(b1, d1, false),
			make_tuple(c1, c2, true),
			make_tuple(c1, d1, false),
			make_tuple(d1, d2, true)
	};

	auto checker = [] (test_data d) {
		auto l = std::get<0>(d);
		auto r = std::get<1>(d);
		auto equality = std::get<2>(d);
		if (equality == true)
			ASSERT_EQ(l, r);
		else
			ASSERT_NE(l, r);
	};

	std::for_each(l.begin(), l.end(), checker);
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

	auto v = V("x");
	for (it_type it = m.begin(); it != m.end(); it++) {
		solver::BinOp op(v, v, it->first);
		EXPECT_EQ(it->second, op.GetKindName());
	}
}

//-------------------------------------------------------------------
// SmartPointers and polymorphism testing
TEST_F(ExprTest, SmartPointer_Comparison_Variable) {
	auto x1 = V("x"),
			x2 = V("x"),
			x3 = V("x"),
			y = V("y");
	EXPECT_EQ(*x1, *x1);	// reflexivity
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
	EXPECT_NE(*x1, *y);
	EXPECT_NE(x1, nullptr);
	EXPECT_NE(nullptr, x1);
}

TEST_F(ExprTest, SmartPointer_Comparison_Constant) {
	std::int32_t val1 = 28, val2 = 99;
	auto x1 = C(val1),
			x2 = C(val1),
			x3 = C(val1),
			y = C(val2);
	EXPECT_EQ(*x1, *x1);	// reflexivity
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
	EXPECT_NE(*x1, *y);
	EXPECT_NE(x1, nullptr);
	EXPECT_NE(nullptr, x1);
}

TEST_F(ExprTest, SmartPointer_Comparison_BinaryOperation) {
	auto v = V("x");
	auto x1  = Apply(v, v, Kind::ADD),
			x2 = Apply(v, v, Kind::ADD),
			x3 = Apply(v, v, Kind::ADD),
			y = Apply(v, v, Kind::SUB);
	EXPECT_EQ(*x1, *x1);	// reflexivity
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
	EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
	EXPECT_NE(*x1, *y);
	EXPECT_NE(x1, nullptr);
	EXPECT_NE(nullptr, x1);
}

TEST_F(ExprTest, SmartPointer_Comparison_CrossTest) {
	auto var = V("var");
	auto c1 = C(28),
			c2 = C(99);
	auto op = Apply(c1, c2, Kind::ADD);
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
	delete v, c;
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












