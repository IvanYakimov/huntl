// Project
#include <cvc4/cvc4.h>
#include "gtest/gtest.h"
#include "../src/instanceof.hpp"
#include "../src/solver.hpp"
#include "../src/holder.hpp"
#include "../src/to_string.hpp"

namespace memory {
	class HolderTest : public ::testing::Test {
	public:
		solver::Solver solver;
	};

	TEST_F(HolderTest, instanceof) {
		using utils::instanceof;
		using interpreter::MetaInt;
		auto bv32 = solver.MkBitVectorType(32);
		auto x = solver.MkVar(bv32);
		auto x_h = Symbolic::Create(x);
		auto x_h2 = Symbolic::Create(x);
		auto i32_h1 = Concrete::Create(MetaInt(32, 42));
		auto i32_h2 = Concrete::Create(MetaInt(32, 42));
		auto i32_hx = Concrete::Create(MetaInt(32, 28));

		// Comparison
		ASSERT_EQ(*i32_h1, *i32_h2);
		ASSERT_NE(*i32_h1, *i32_hx);
		ASSERT_EQ(*x_h, *x_h2);

		// Showing
		ASSERT_EQ(utils::to_string(*i32_h1), "42");
		ASSERT_EQ(utils::to_string(*x_h), "var_161");

		// Type Checking
		ASSERT_TRUE(instanceof<Holder>(x_h));
		ASSERT_TRUE(instanceof<Symbolic>(x_h));
		ASSERT_FALSE(instanceof<Concrete>(x_h));

		ASSERT_TRUE(instanceof<Holder>(i32_h1));
		ASSERT_TRUE(instanceof<Concrete>(i32_h1));
		ASSERT_FALSE(instanceof<Symbolic>(i32_h1));

		ASSERT_TRUE(IsSymbolic(x_h));
		ASSERT_FALSE(IsConcrete(x_h));

		ASSERT_TRUE(IsConcrete(i32_h1));
		ASSERT_FALSE(IsSymbolic(i32_h1));
	}
}














