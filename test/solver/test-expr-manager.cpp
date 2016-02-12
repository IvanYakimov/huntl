#include "gtest/gtest.h"
#include "../../src/solver/expr-manager.hpp"

namespace solver {
	class ExprManagerTest : public ::testing::Test {
	public:
		ExprManager em;
	};

	TEST_F(ExprManagerTest, MkTy) {
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
				make_tuple(i8ty, em.MkTy<SInt8Ty>(), true),
				make_tuple(i16ty, em.MkTy<SInt16Ty>(), true),
				make_tuple(i32ty, em.MkTy<SInt32Ty>(), true),
				make_tuple(i64ty, em.MkTy<SInt64Ty>(), true),
				make_tuple(ui8ty, em.MkTy<UInt8Ty>(), true),
				make_tuple(ui16ty, em.MkTy<UInt16Ty>(), true),
				make_tuple(ui32ty, em.MkTy<UInt32Ty>(), true),
				make_tuple(ui64ty, em.MkTy<UInt64Ty>(), true),
				make_tuple(i8ty, em.MkTy<SInt32Ty>(), false)
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














