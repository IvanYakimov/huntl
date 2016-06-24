// Project
#include <cvc4/cvc4.h>
#include "gtest/gtest.h"
#include "../src/instanceof.hpp"
#include "../src/solver.hpp"
#include "../src/holder.hpp"

namespace memory {
	class HolderTest : public ::testing::Test {
	public:
		solver::Solver solver;
	};

	TEST_F(HolderTest, instanceof) {
		using utils::instanceof;
		auto bv32 = solver.ExprManager().mkBitVectorType(32);
		auto x = solver.ExprManager().mkVar(bv32);
		auto c = solver.ExprManager().mkConst(CVC4::BitVector(32, 256U));
		auto e = solver.ExprManager().mkExpr(CVC4::Kind::EQUAL, x, c);
		auto e_holder = Symbolic::Create(e);
		auto i32_h1 = ObjHolder<uint32_t>::Create(42);
		auto i32_h2 = ObjHolder<uint32_t>::Create(42);
		auto i16_h = ObjHolder<uint16_t>::Create(42);
		auto nil_holder = Undef::Create();

		ASSERT_EQ(*i32_h1, *i32_h2);
		ASSERT_EQ(*i32_h1, *i16_h);

		ASSERT_TRUE(instanceof<Holder>(e_holder));
		ASSERT_TRUE(instanceof<Symbolic>(e_holder));
		ASSERT_FALSE(instanceof<Undef>(e_holder));
		ASSERT_FALSE(instanceof<ObjHolder<uint32_t>>(e_holder));

		ASSERT_TRUE(instanceof<Holder>(nil_holder));
		ASSERT_TRUE(instanceof<Undef>(nil_holder));
		ASSERT_FALSE(instanceof<Symbolic>(nil_holder));
		ASSERT_FALSE(instanceof<ObjHolder<uint32_t>>(nil_holder));

		ASSERT_TRUE(instanceof<Holder>(i32_h1));
		ASSERT_TRUE(instanceof<ObjHolder<uint32_t>>(i32_h1));
		ASSERT_FALSE(instanceof<Symbolic>(i32_h1));
		ASSERT_FALSE(instanceof<ObjHolder<uint16_t>>(i32_h1));

		ASSERT_TRUE(IsSymbolic(e_holder));
		ASSERT_FALSE(IsConcrete(e_holder));
		ASSERT_FALSE(IsUndef(e_holder));

		ASSERT_TRUE(IsConcrete(i32_h1));
		ASSERT_FALSE(IsSymbolic(i32_h1));
		ASSERT_FALSE(IsUndef(i32_h1));

		ASSERT_TRUE(IsUndef(nil_holder));
		ASSERT_FALSE(IsSymbolic(nil_holder));
		ASSERT_FALSE(IsConcrete(nil_holder));
	}
}














