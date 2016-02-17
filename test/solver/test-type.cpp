// Project
#include "../../src/solver/type.hpp"

// Google Test
# include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>
#include <list>
#include <array>

namespace solver {
	class TypeTest : public ::testing::Test {
	public:
		template<typename T>
		TypePtr MkTy() { return std::make_shared<IntTy<T>>(); }
	};

	//TODO: combinatorial testing
	TEST_F(TypeTest, Comparison) {
		using namespace std;
		TypePtr x1 = MkTy<int32_t>(),
				x2 = MkTy<int32_t>(),
				x3 = MkTy<int32_t>(),
				y = MkTy<int16_t>();

		EXPECT_EQ(*x1, *x1);
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1);
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3);

		EXPECT_NE(*x1, *y);
		EXPECT_NE(x1, nullptr);
		EXPECT_NE(nullptr, x1);
	}

	TEST_F(TypeTest, Comb_Comparison) {
		using namespace std;
		array<TypePtr, 8> val_list = {
				MkTy<int8_t>(),
				MkTy<int16_t>(),
				MkTy<int32_t>(),
				MkTy<int64_t>(),
				MkTy<uint8_t>(),
				MkTy<uint16_t>(),
				MkTy<uint32_t>(),
				MkTy<uint64_t>()
		};

		int l = val_list.size();
		for (auto i = 0; i != l; i++)
			for (auto j = 0; j != l; j++)
				if (i == j)
					ASSERT_EQ(val_list[i], val_list[j]);
				else
					ASSERT_NE(val_list[i], val_list[j]);
	}

	TEST_F(TypeTest, Validity) {
		using namespace std;
		using the_tuple = std::tuple<TypePtr, bool, Alignment, Width>;
		using the_list = std::list<the_tuple>;

		auto checker = [] (the_tuple tpl) -> bool{
				auto ty = get<0>(tpl);
		};

		the_list val_list = {
				make_tuple(MkTy<std::int8_t>(), true, 1, Width::w8),
				make_tuple(MkTy<std::int16_t>(), true, 2, Width::w16),
				make_tuple(MkTy<std::int32_t>(), true, 4, Width::w32),
				make_tuple(MkTy<std::int64_t>(), true, 8, Width::w64),
				make_tuple(MkTy<std::uint8_t>(), false, 1, Width::w8),
				make_tuple(MkTy<std::uint16_t>(), false, 2, Width::w16),
				make_tuple(MkTy<std::uint32_t>(), false, 4, Width::w32),
				make_tuple(MkTy<std::uint64_t>(), false, 8, Width::w64)
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}
}













