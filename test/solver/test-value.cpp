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
		ValuePtr MkIntVal(T val) {return std::make_shared<Int<T>>(val);}
	};

	TEST_F(ValueTest, Comparison) {
		int c = 42,
				c2 = 170;

		ValuePtr x1 = MkIntVal<std::int32_t>(c),
				x2 = MkIntVal<std::int32_t>(c),
				x3 = MkIntVal<std::int32_t>(c),
				y = MkIntVal<std::int32_t>(c2),	// c2!
				z = MkIntVal<std::int16_t>(c);	// std::int16_t!

		EXPECT_EQ(*x1, *x1);	// reflexivity
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x1); // symmetry
		EXPECT_EQ(*x1, *x2); EXPECT_EQ(*x2, *x3); EXPECT_EQ(*x1, *x3);	// transitivity

		EXPECT_NE(*x1, *y);
		EXPECT_NE(*x1, *z);
		EXPECT_NE(x1, nullptr);
		EXPECT_NE(nullptr, x1);
	}

	TEST_F(ValueTest, Comb_Comparison) {
		//TODO: combinatorial testing
		// for each combination of type and value
	}


	TEST_F(ValueTest, Cast) {
		ValuePtr val1 = MkIntVal<std::int32_t>(42);

		ASSERT_TRUE(instanceof<Value>(val1));
		ASSERT_TRUE(instanceof<BasicInt>(val1));
		ASSERT_TRUE(instanceof<Int<int32_t>>(val1));

		ASSERT_FALSE(instanceof<Int<int8_t>>(val1));
		ASSERT_FALSE(instanceof<Int<int16_t>>(val1));
		ASSERT_FALSE(instanceof<Int<int64_t>>(val1));
	}

	TEST_F(ValueTest, Comb_Cast) {
		//TODO: combinatorial testing
		// for each type of IntVal
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
				make_tuple(MkIntVal<std::int8_t>(0), true, 1, Width::w8),
				make_tuple(MkIntVal<std::int16_t>(0), true, 2, Width::w16),
				make_tuple(MkIntVal<std::int32_t>(0), true, 4, Width::w32),
				make_tuple(MkIntVal<std::int64_t>(0), true, 8, Width::w64),

				make_tuple(MkIntVal<std::uint8_t>(0), false, 1, Width::w8),
				make_tuple(MkIntVal<std::uint16_t>(0), false, 2, Width::w16),
				make_tuple(MkIntVal<std::uint32_t>(0), false, 4, Width::w32),
				make_tuple(MkIntVal<std::uint64_t>(0), false, 8, Width::w64)
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}

	namespace ability_test{
	template<typename T>
	void helper() {
		using namespace std;
		ASSERT_TRUE(numeric_limits<T>::is_integer);

		auto min = numeric_limits<T>::min();
		auto max = numeric_limits<T>::max();
		auto checker = [&] (T val) -> void {
			shared_ptr<BasicInt> first = make_shared<Int<T>>(val);
			shared_ptr<BasicInt> second = make_shared<Int<T>>();
			auto l = first->GetUInt64();
			ASSERT_EQ(8, sizeof(l));
			second->SetUInt64(l);
			//cout << *first << " val to long: " << l << ", back to val: " << *second << endl;
			ASSERT_EQ(val, (dynamic_pointer_cast<Int<T>>(second))->GetVal());
		};

		std::list<T> val_list = {
				min,
				max,
				0,
				42
		};

		if (std::numeric_limits<T>::is_signed)
			val_list.push_back(-42);

		for_each(val_list.begin(), val_list.end(), checker);
	}

	void body() {
		helper<int8_t>();
		helper<int16_t>();
		helper<int32_t>();
		helper<int64_t>();
		helper<uint8_t>();
		helper<uint16_t>();
		helper<uint32_t>();
		helper<uint64_t>();
	};
	}

	TEST_F(ValueTest, Ability) {
		ability_test::body();
	}

	//TODO:
	//ToString
	//GedWidth
	//GetAlignment
}














