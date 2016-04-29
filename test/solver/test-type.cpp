// Project
#include "../../src/solver/type.hpp"
#include "../../src/solver/expr.hpp"
#include "../../src/solver/value.hpp"
#include "../../src/utils/object.hpp"

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

	TEST_F(TypeTest, DISABLED_Constructor) {
		throw std::logic_error("not implemented");
	}

	TEST_F(TypeTest, DISABLED_Destructor) {
		throw std::logic_error("not implemented");
	}

	TEST_F(TypeTest, Equals) {
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

	TEST_F(TypeTest, Equals_combinatorial) {
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

	TEST_F(TypeTest, ToString_GetWidth_IsSigned) {
		using namespace std;
		using the_tuple = std::tuple<TypePtr, string, bool, Width>;
		using the_list = std::list<the_tuple>;

		auto checker = [] (the_tuple tpl) -> bool{
			auto ty = dynamic_pointer_cast<BasicIntTy>(get<0>(tpl));
			auto name = get<1>(tpl);
			auto sign = get<2>(tpl);
			auto width = get<3>(tpl);
			EXPECT_EQ(name, ty->ToString());
			EXPECT_EQ(sign, ty->IsSigned());
			EXPECT_EQ(width, ty->GetWidth());
		};

		the_list val_list = {
				make_tuple(MkTy<std::int8_t>(), "i8", true, Width::w8),
				make_tuple(MkTy<std::int16_t>(), "i16", true, Width::w16),
				make_tuple(MkTy<std::int32_t>(), "i32", true, Width::w32),
				make_tuple(MkTy<std::int64_t>(), "i64", true, Width::w64),
				make_tuple(MkTy<std::uint8_t>(), "ui8", false, Width::w8),
				make_tuple(MkTy<std::uint16_t>(), "ui16", false, Width::w16),
				make_tuple(MkTy<std::uint32_t>(), "ui32", false, Width::w32),
				make_tuple(MkTy<std::uint64_t>(), "ui64", false, Width::w64)
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}

	TEST_F(TypeTest, instanceof) {
		TypePtr ty = MkTy<int32_t>();
		ASSERT_TRUE(instanceof<Object>(ty));
		ASSERT_TRUE(instanceof<Type>(ty));
		ASSERT_TRUE(instanceof<BasicIntTy>(ty));
		ASSERT_TRUE(instanceof<IntTy<int32_t>>(ty));

		ASSERT_FALSE(instanceof<IntTy<int16_t>>(ty));

		ASSERT_FALSE(instanceof<Expr>(ty));
		ASSERT_FALSE(instanceof<Var>(ty));
		ASSERT_FALSE(instanceof<Const>(ty));
		ASSERT_FALSE(instanceof<BinOp>(ty));
		ASSERT_FALSE(instanceof<Value>(ty));
		ASSERT_FALSE(instanceof<BasicInt>(ty));
	}

	TEST_F(TypeTest, singleton) {
		auto ty1 = IntTy<int8_t>::Get();
		auto ty2 = IntTy<int8_t>::Get();
		ASSERT_EQ(ty1, ty2);
		ASSERT_EQ(*ty1, *ty2);
	}
}













