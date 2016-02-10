// Project
#include "../../src/solver/value.hpp"

// Google Test
# include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>
#include <list>

namespace solver {
	class ValueTest : public ::testing::Test {
	public:
		template<typename T>
		ValuePtr MkRawInt(T val) {return std::make_shared<Int<T>>(val);}
	};

	TEST_F(ValueTest, Comparison) {
		int c = 42,
				c2 = 170;

		ValuePtr x1 = MkRawInt<std::int32_t>(c),
				x2 = MkRawInt<std::int32_t>(c),
				x3 = MkRawInt<std::int32_t>(c),
				y = MkRawInt<std::int32_t>(c2),	// c2!
				z = MkRawInt<std::int16_t>(c);	// std::int16_t!

		EXPECT_EQ(*x1, *x1);	// reflexivity
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetry
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3);	// transitivity

		EXPECT_NE(*x1, *y);
		EXPECT_NE(*x1, *z);
		EXPECT_NE(x1, nullptr);
		EXPECT_NE(nullptr, x1);
	}

	//TODO: parametrized combinatorial testing
	TEST_F(ValueTest, Cast) {
		ValuePtr val1 = MkRawInt<std::int32_t>(42);

		ASSERT_TRUE(instanceof<Value>(val1));
		ASSERT_TRUE(instanceof<BasicInt>(val1));
		ASSERT_TRUE(instanceof<SInt32>(val1));

		ASSERT_FALSE(instanceof<SInt8>(val1));
		ASSERT_FALSE(instanceof<SInt16>(val1));
		ASSERT_FALSE(instanceof<SInt64>(val1));
	}

	TEST_F(ValueTest, IsSigned) {
		using std::make_tuple;
		using std::dynamic_pointer_cast;
		using std::get;
		using the_tuple = std::tuple<ValuePtr, bool, Alignment, Width>;
		using the_list = std::list<the_tuple>;

		auto checker = [] (the_tuple t) -> void {
			auto val = dynamic_pointer_cast<BasicInt>(get<0>(t));
			auto is_sign = get<1>(t);
			auto align = get<2>(t);
			auto width = get<3>(t);
			ASSERT_EQ(is_sign, val->IsSigned());
			ASSERT_EQ(align, val->GetAlignment());
			ASSERT_EQ(width, val->GetWidth());
		};

		the_list val_list = {
				make_tuple(MkRawInt<std::int8_t>(0), true, 1, 8),
				make_tuple(MkRawInt<std::int16_t>(0), true, 2, 16),
				make_tuple(MkRawInt<std::int32_t>(0), true, 4, 32),
				make_tuple(MkRawInt<std::int64_t>(0), true, 8, 64),

				make_tuple(MkRawInt<std::uint8_t>(0), false, 1, 8),
				make_tuple(MkRawInt<std::uint16_t>(0), false, 2, 16),
				make_tuple(MkRawInt<std::uint32_t>(0), false, 4, 32),
				make_tuple(MkRawInt<std::uint64_t>(0), false, 8, 64)
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}

	//TODO:
	//ToString
	//GedWidth
	//GetAlignment
}














