// Project
#include "../../src/solver/type.hpp"

// Google Test
# include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>
#include <list>

namespace solver {
	class TypeTest : public ::testing::Test {
	public:
		template<typename T>
		SharedType MkTy() { return std::make_shared<RawIntType<T>>(); }
	};

	TEST_F(TypeTest, Comparison) {
		using namespace std;
		SharedType x1 = MkTy<int32_t>(),
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

	TEST_F(TypeTest, Validity) {
		using namespace std;
		using the_tuple = std::tuple<SharedType, bool, Alignment, Width>;
		using the_list = std::list<the_tuple>;

		auto checker = [] (the_tuple tpl) -> bool{
				auto ty = get<0>(tpl);

		};

		the_list val_list = {
				make_tuple(MkTy<std::int8_t>(), true, 1, 8),
				make_tuple(MkTy<std::int16_t>(), true, 2, 16),
				make_tuple(MkTy<std::int32_t>(), true, 4, 32),
				make_tuple(MkTy<std::int64_t>(), true, 8, 64),
				make_tuple(MkTy<std::uint8_t>(), false, 1, 8),
				make_tuple(MkTy<std::uint16_t>(), false, 2, 16),
				make_tuple(MkTy<std::uint32_t>(), false, 4, 32),
				make_tuple(MkTy<std::uint64_t>(), false, 8, 64)
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}
}













