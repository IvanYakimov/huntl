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
		auto x = solver.ExprManager().mkVar("x", bv32);
		auto x_h = Symbolic::Create(x);
		auto x_h2 = Symbolic::Create(x);
		auto i32_h1 = ObjHolder<uint32_t>::Create(42);
		auto i32_h2 = ObjHolder<uint32_t>::Create(42);
		auto i16_h = ObjHolder<uint16_t>::Create(42);
		auto nil_holder = Undef::Create();

		// Comparison
		ASSERT_EQ(*i32_h1, *i32_h2);
		ASSERT_NE(*i32_h1, *i16_h);
		ASSERT_EQ(*x_h, *x_h2);

		// Showing
		ASSERT_EQ(i32_h1->ToString(), "42");
		ASSERT_EQ(x_h->ToString(), x.toString());

		// Type Checking
		ASSERT_TRUE(instanceof<Holder>(x_h));
		ASSERT_TRUE(instanceof<Symbolic>(x_h));
		ASSERT_FALSE(instanceof<Undef>(x_h));
		ASSERT_FALSE(instanceof<ObjHolder<uint32_t>>(x_h));

		ASSERT_TRUE(instanceof<Holder>(nil_holder));
		ASSERT_TRUE(instanceof<Undef>(nil_holder));
		ASSERT_FALSE(instanceof<Symbolic>(nil_holder));
		ASSERT_FALSE(instanceof<ObjHolder<uint32_t>>(nil_holder));

		ASSERT_TRUE(instanceof<Holder>(i32_h1));
		ASSERT_TRUE(instanceof<ObjHolder<uint32_t>>(i32_h1));
		ASSERT_FALSE(instanceof<Symbolic>(i32_h1));
		ASSERT_FALSE(instanceof<ObjHolder<uint16_t>>(i32_h1));

		ASSERT_TRUE(IsSymbolic(x_h));
		ASSERT_FALSE(IsConcrete(x_h));
		ASSERT_FALSE(IsUndef(x_h));

		ASSERT_TRUE(IsConcrete(i32_h1));
		ASSERT_FALSE(IsSymbolic(i32_h1));
		ASSERT_FALSE(IsUndef(i32_h1));

		ASSERT_TRUE(IsUndef(nil_holder));
		ASSERT_FALSE(IsSymbolic(nil_holder));
		ASSERT_FALSE(IsConcrete(nil_holder));
	}
}














