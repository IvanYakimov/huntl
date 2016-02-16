#include "gtest/gtest.h"
#include "../../src/solver/expr-manager.hpp"

namespace solver {
	class ExprManagerTest : public ::testing::Test {
	public:
		ExprManager em;
	};

	TEST_F(ExprManagerTest, MkVal) {
		int val = 42;
		auto produced_item = em.MkIntVal<int8_t>(val);
		auto item = std::make_shared<Int<int8_t>>(val);
		ASSERT_EQ(*item, *produced_item);
	}


	TEST_F(ExprManagerTest, MkTy) {
		//TODO: this kind of testing is redundant (in current implementation of ExprManager)
		using namespace std;

		auto i8ty = make_shared<IntTy<int8_t>>();
		auto i16ty = make_shared<IntTy<int16_t>>();
		auto i32ty = make_shared<IntTy<int32_t>>();
		auto i64ty = make_shared<IntTy<int64_t>>();
		auto ui8ty = make_shared<IntTy<uint8_t>>();
		auto ui16ty = make_shared<IntTy<uint16_t>>();
		auto ui32ty = make_shared<IntTy<uint32_t>>();
		auto ui64ty = make_shared<IntTy<uint64_t>>();

		using the_tuple = tuple<TypePtr, TypePtr, bool>;
		using the_list = list<the_tuple>;

		the_list val_list = {
				make_tuple(i8ty, em.MkIntTy<int8_t>(), true),
				make_tuple(i16ty, em.MkIntTy<int16_t>(), true),
				make_tuple(i32ty, em.MkIntTy<int32_t>(), true),
				make_tuple(i64ty, em.MkIntTy<int64_t>(), true),
				make_tuple(ui8ty, em.MkIntTy<uint8_t>(), true),
				make_tuple(ui16ty, em.MkIntTy<uint16_t>(), true),
				make_tuple(ui32ty, em.MkIntTy<uint32_t>(), true),
				make_tuple(ui64ty, em.MkIntTy<uint64_t>(), true),
				make_tuple(i8ty, em.MkIntTy<uint32_t>(), false)
		};

		auto checker = [] (the_tuple tpl) {
			TypePtr left = get<0>(tpl);
			TypePtr right = get<1>(tpl);
			bool expect = get<2>(tpl);
			if (expect == true)
				EXPECT_EQ(*left, *right);
			else
				EXPECT_NE(*left, *right);
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}
}














