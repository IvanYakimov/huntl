// useful links:
// https://github.com/google/googletest/blob/master/googletest/docs/Primer.mdy

// Project
#include "../../src/solver/expr.hpp"
#include "../../src/utils/object.hpp"

// Google Test
#include "gtest/gtest.h"

// STL
#include <memory>
#include <string>
#include <iostream>
#include <map>
#include <list>
#include <tuple>
#include <functional>
#include "../../src/solver/object-builder.hpp"

using std::shared_ptr;

namespace solver {
	class ExprTest : public ::testing::Test {
		public:
			ObjectBuilder em;
	};

	//-------------------------------------------------------------------
	// Variable

	TEST_F(ExprTest, Variable_Creation) {
		using namespace std;
		using the_tuple = tuple<string, TypePtr, bool>;
		using the_list = list<the_tuple>;

		the_list val_list = {
				//make_tuple(nullptr, nullptr, true),
				make_tuple("", nullptr, true),
				make_tuple("x", nullptr, true),
				make_tuple("x", em.MkIntTy<int32_t>(), false)
		};

		auto checker = [] (the_tuple tpl) {
			string name = get<0>(tpl);
			TypePtr ty = get<1>(tpl);
			bool throws_exception = get<2>(tpl);
			bool thrown = false;
			try {
				Var v(name, ty);
			}
			catch (IllegalArgException &ex) {
				thrown = true;
			}
			ASSERT_EQ(throws_exception, thrown);
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}


	TEST_F(ExprTest, Variable_Accessors) {
		using namespace std;
		Var v("x", em.MkIntTy<int32_t>());
		//EXPECT_EQ("i32 x", v.ToString());
		EXPECT_EQ("x", v.GetName());
		EXPECT_EQ(em.MkIntTy<int32_t>(), v.GetType());
	}


	TEST_F(ExprTest, Variable_Comparison) {
		auto i32ty = em.MkIntTy<int32_t>();
		auto i16ty = em.MkIntTy<int16_t>();
		Var x1("x", i32ty),
					x2("x", i32ty),
					y("y", i32ty),
					x_16("x",i16ty);
		EXPECT_EQ(x1, x1); // reflexivity
		EXPECT_NE(x1, x2); EXPECT_NE(x2, x1);
		EXPECT_NE(x1, y);
		EXPECT_NE(x1, x_16);
		EXPECT_NE(&x1, nullptr);
		EXPECT_NE(nullptr, &x1);
	}

	//-------------------------------------------------------------------
	// Constant

	// TODO: creation test
	TEST_F(ExprTest, Constant_Creation) {
		try {
			Const(nullptr);
			FAIL();
		}
		catch (IllegalArgException &e) {}
	}

	TEST_F(ExprTest, Constant_Accessors) {
		auto val = em.MkIntVal<int32_t>(42);
		Const x = Const(val);
		EXPECT_EQ(*val, *x.GetValue());
		EXPECT_EQ(val->ToString(), x.ToString());
	}

	TEST_F(ExprTest, Constant_Comparison) {
		auto val1 = em.MkIntVal<int32_t>(42);
		auto val2 = em.MkIntVal<int32_t>(170);
		Const x1(val1),
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
		auto v = em.MkVar("x", em.MkIntTy<int32_t>());
		bool s1 = false,
				s2 = false,
				s3 = false,
				s4 = false;
		try {
			BinOp b(nullptr, v, Kind::ADD);
			FAIL();
		}
		catch (IllegalArgException &e) {}

		try {
			BinOp b(v, nullptr, Kind::ADD);
			FAIL();
		}
		catch (IllegalArgException &e) {}

		try {
			BinOp b(nullptr, nullptr, Kind::ADD);
			FAIL();
		}
		catch (IllegalArgException &e) {}

		try {
			BinOp b(v, v, Kind::ADD);
		}
		catch (IllegalArgException &e) {
			FAIL();
		}
	}


	TEST_F(ExprTest, BinOp_Accessors) {
		auto ty = em.MkIntTy<int32_t>();
		auto left = em.MkVar("x", ty);
		auto right = em.MkVar("y", ty);
		BinOp bin_op(left, right, solver::Kind::ADD);

		EXPECT_EQ(left, bin_op.GetLeftChild());
		EXPECT_EQ(right, bin_op.GetRightChild());
		EXPECT_EQ(Kind::ADD, bin_op.GetKind());
		//EXPECT_EQ("(add i32 x i32 y)", bin_op.ToString());
	}


	TEST_F(ExprTest, BinaryOp_Comparison_Basic) {
		auto ty = em.MkIntTy<int32_t>();
		auto v = em.MkVar("x", ty);
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
		auto ty = em.MkIntTy<int32_t>();
		auto x = em.MkVar("x", ty),
				y = em.MkVar("y", ty);

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
				// arithmetical
				{Kind::ADD, "add"},
				{Kind::SUB, "sub"},
				{Kind::MUL, "mul"},
				{Kind::SHL, "shl"},
				{Kind::LSHR, "lshr"},
				{Kind::ASHR, "ashr"},

				// logical
				{Kind::AND, "and"},
				{Kind::OR, "or"},
				{Kind::XOR, "xor"},

				// Comparisons
				{Kind::EQUAL, "eq"},
				{Kind::DISTINCT, "distinct"},
				{Kind::UGE, "uge"},
				{Kind::UGT, "ugt"},
				{Kind::ULE, "ule"},
				{Kind::ULT, "ult"},
				{Kind::SGT, "sgt"},
				{Kind::SGE, "sge"},
				{Kind::SLT, "slt"},
				{Kind::SLE, "sle"}
		};

		auto ty = em.MkIntTy<int32_t>();
		auto v = em.MkVar("x", ty);
		for (it_type it = m.begin(); it != m.end(); it++) {
			solver::BinOp op(v, v, it->first);
			EXPECT_EQ(it->second, op.GetKindName());
		}
	}


	//-------------------------------------------------------------------
	// SmartPointers and polymorphism testing
	TEST_F(ExprTest, SmartPointer_Comparison_Variable) {
		auto ty = em.MkIntTy<int32_t>();
		auto x1 = em.MkVar("x", ty),
				x2 = em.MkVar("x", ty),
				y = em.MkVar("y", ty);
		EXPECT_EQ(*x1, *x1);
		EXPECT_NE(*x1, *x2); EXPECT_NE(*x2, *x1);
		EXPECT_NE(*x1, *y);
		EXPECT_NE(x1, nullptr);
		EXPECT_NE(nullptr, x1);
	}


	TEST_F(ExprTest, SmartPointer_Comparison_Constant) {
		auto val1 = em.MkIntVal<int32_t>(42);
		auto val2 = em.MkIntVal<int32_t>(170);
		auto x1 = em.MkConst(val1),
				x2 = em.MkConst(val1),
				x3 = em.MkConst(val1),
				y = em.MkConst(val2);
		EXPECT_EQ(*x1, *x1);	// reflexivity
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
		EXPECT_NE(*x1, *y);
		EXPECT_NE(x1, nullptr);
		EXPECT_NE(nullptr, x1);
	}


	TEST_F(ExprTest, SmartPointer_Comparison_BinaryOperation) {
		auto ty = em.MkIntTy<int32_t>();
		auto v = em.MkVar("x", ty);
		auto x1  = em.MkBinOp(v, v, Kind::ADD),
				x2 = em.MkBinOp(v, v, Kind::ADD),
				x3 = em.MkBinOp(v, v, Kind::ADD),
				y = em.MkBinOp(v, v, Kind::SUB);
		EXPECT_EQ(*x1, *x1);	// reflexivity
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetric
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3); // transivity
		EXPECT_NE(*x1, *y);
		EXPECT_NE(x1, nullptr);
		EXPECT_NE(nullptr, x1);
	}


	TEST_F(ExprTest, SmartPointer_Comparison_CrossTest) {
		auto ty = em.MkIntTy<int32_t>();
		auto var = em.MkVar("var", ty);
		auto val1 = em.MkIntVal<int32_t>(42),
				val2 = em.MkIntVal<int32_t>(170);
		auto c1 = em.MkConst(val1),
				c2 = em.MkConst(val2);
		auto op = em.MkBinOp(c1, c2, Kind::ADD);
		EXPECT_NE(*var, *c1);
		EXPECT_NE(*c1, *var);
		EXPECT_NE(*var, *op);
		EXPECT_NE(*op, *var);
		EXPECT_NE(*c1, *op);
		EXPECT_NE(*op, *c1);
	}

	//-------------------------------------------------------------------
	// Casting
	TEST_F(ExprTest, Cast) {
		auto ty = em.MkIntTy<int32_t>();
		auto val = em.MkIntVal<int32_t>(42);
		Expr *v = new Var("x", ty),
				*c = new Const(val);
		auto p1 = dynamic_cast<Const*>(v);
		auto p2 = dynamic_cast<Var*>(c);
		ASSERT_EQ(nullptr, p1);
		ASSERT_EQ(nullptr, p2);
		delete v, c;
	}

	TEST_F(ExprTest, PointerCast) {
		auto ty = em.MkIntTy<int32_t>();
		auto val = em.MkIntVal<int32_t>(42);
		ExprPtr v = em.MkVar("x", ty),
				c = em.MkConst(val),
				b = em.MkBinOp(v, c, Kind::EQUAL);

		auto pvv = std::dynamic_pointer_cast<Var>(v);
		auto pvc = std::dynamic_pointer_cast<Const>(v);
		auto pvb = std::dynamic_pointer_cast<BinOp>(v);

		auto pcv = std::dynamic_pointer_cast<Var>(c);
		auto pcc = std::dynamic_pointer_cast<Const>(c);
		auto pcb = std::dynamic_pointer_cast<BinOp>(c);

		auto pbv = std::dynamic_pointer_cast<Var>(b);
		auto pbc = std::dynamic_pointer_cast<Const>(b);
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

	TEST_F(ExprTest, InstanceOf) {
		auto ty = em.MkIntTy<int32_t>();
		auto val = em.MkIntVal<int32_t>(42);
		ExprPtr v = em.MkVar("x", ty),
				c = em.MkConst(val),
				b = em.MkBinOp(v, c, Kind::EQUAL);

		// Variable
		ASSERT_TRUE(instanceof<Object>(v));
		ASSERT_TRUE(instanceof<Immutable>(v));
		ASSERT_FALSE(instanceof<Mutable>(v));
		ASSERT_TRUE(instanceof<Expr>(v));
		ASSERT_TRUE(instanceof<Var>(v));
		ASSERT_FALSE(instanceof<Const>(v));
		ASSERT_FALSE(instanceof<BinOp>(v));

		ASSERT_TRUE(instanceof<Object>(c));
		ASSERT_TRUE(instanceof<Immutable>(c));
		ASSERT_FALSE(instanceof<Mutable>(c));
		ASSERT_TRUE(instanceof<Expr>(c));
		ASSERT_FALSE(instanceof<Var>(c));
		ASSERT_TRUE(instanceof<Const>(c));
		ASSERT_FALSE(instanceof<BinOp>(c));

		ASSERT_TRUE(instanceof<Object>(b));
		ASSERT_TRUE(instanceof<Immutable>(b));
		ASSERT_FALSE(instanceof<Mutable>(b));
		ASSERT_TRUE(instanceof<Expr>(b));
		ASSERT_FALSE(instanceof<Var>(b));
		ASSERT_FALSE(instanceof<Const>(b));
		ASSERT_TRUE(instanceof<BinOp>(b));
	}

}












