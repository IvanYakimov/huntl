#include "gtest/gtest.h"

#include "../../src/solver/object-builder.hpp"

namespace solver {
	class ExprManagerTest : public ::testing::Test {
	public:
		ObjectBuilder em;
	};

	//TODO: extract singleton test
	//Singleton test
	TEST_F(ExprManagerTest, GetExprManager) {
		ObjectBuilderPtr em_1 = ObjectBuilder::Get();
		ObjectBuilderPtr em_2 = ObjectBuilder::Get();
		ObjectBuilderPtr em_3 = ObjectBuilder::Get();
		ASSERT_NE(em_1, nullptr);
		ASSERT_EQ(em_1, em_2); ASSERT_EQ(em_2, em_3); ASSERT_EQ(em_1, em_3);
	}

	TEST_F(ExprManagerTest, MkVar) {
		auto name = "x";
		auto ty = em.MkIntTy<int32_t>();
		auto expr = em.MkVar(name, ty);
		ASSERT_TRUE(instanceof<Var>(expr));
		auto var = std::dynamic_pointer_cast<Var>(expr);
		ASSERT_EQ(name, var->GetName());
		ASSERT_EQ(ty, var->GetType());
	}

	TEST_F(ExprManagerTest, MkConst) {
		auto val = em.MkIntVal<int32_t>(42);
		auto expr = em.MkConst(val);
		ASSERT_TRUE(instanceof<Const>(expr));
		auto c = std::dynamic_pointer_cast<Const>(expr);
		ASSERT_EQ(val, c->GetValue());
	}

	TEST_F(ExprManagerTest, MkBinOp) {
		auto name1 = "x",
				name2 = "y";
		auto ty = em.MkIntTy<int32_t>();
		auto v1 = em.MkVar(name1, ty),
				v2 = em.MkVar(name2, ty);
		auto expr = em.MkBinOp(v1, v2, Kind::ADD);
		ASSERT_TRUE(instanceof<BinOp>(expr));
		auto binop = std::dynamic_pointer_cast<BinOp>(expr);
		ASSERT_EQ(v1, binop->GetLeftChild());
		ASSERT_EQ(v2, binop->GetRightChild());
	}

	TEST_F(ExprManagerTest, MkIntVal_FromULong) {
			using namespace std;
			using Equality = bool;
			ObjectBuilderPtr em_ = ObjectBuilder::Get();
			uint64_t val = 42;

			auto i8ty = em_->MkIntVal(true, Width::w8, val);
			auto i16ty = em_->MkIntVal(true, Width::w16, val);
			auto i32ty = em_->MkIntVal(true, Width::w32, val);
			auto i64ty = em_->MkIntVal(true, Width::w64, val);
			auto ui8ty = em_->MkIntVal(false, Width::w8, val);
			auto ui16ty = em_->MkIntVal(false, Width::w16, val);
			auto ui32ty = em_->MkIntVal(false, Width::w32, val);
			auto ui64ty = em_->MkIntVal(false, Width::w64, val);

			using the_tuple = tuple<ValuePtr, ValuePtr, Equality>;
			using the_list = list<the_tuple>;

			the_list val_list = {
					make_tuple(i8ty, em.MkIntVal<int8_t>(val), true),
					make_tuple(i16ty, em.MkIntVal<int16_t>(val), true),
					make_tuple(i32ty, em.MkIntVal<int32_t>(val), true),
					make_tuple(i64ty, em.MkIntVal<int64_t>(val), true),
					make_tuple(ui8ty, em.MkIntVal<uint8_t>(val), true),
					make_tuple(ui16ty, em.MkIntVal<uint16_t>(val), true),
					make_tuple(ui32ty, em.MkIntVal<uint32_t>(val), true),
					make_tuple(ui64ty, em.MkIntVal<uint64_t>(val), true),
					make_tuple(i8ty, em.MkIntVal<uint32_t>(val), false)
			};

			auto checker = [] (the_tuple tpl) {
				ValuePtr left = get<0>(tpl);
				ValuePtr right = get<1>(tpl);
				bool expect = get<2>(tpl);
				if (expect == true)
					EXPECT_EQ(*left, *right);
				else
					EXPECT_NE(*left, *right);
			};

			for_each(val_list.begin(), val_list.end(), checker);
		}

	TEST_F(ExprManagerTest, MkIntVal) {
		int val = 42;
		auto produced_item = em.MkIntVal<int8_t>(val);
		auto item = std::make_shared<IntVal<int8_t>>(val);
		ASSERT_EQ(*item, *produced_item);
	}

	TEST_F(ExprManagerTest, MkTy) {
		using namespace std;
		using Equality = bool;

		auto i8ty = make_shared<IntTy<int8_t>>();
		auto i16ty = make_shared<IntTy<int16_t>>();
		auto i32ty = make_shared<IntTy<int32_t>>();
		auto i64ty = make_shared<IntTy<int64_t>>();
		auto ui8ty = make_shared<IntTy<uint8_t>>();
		auto ui16ty = make_shared<IntTy<uint16_t>>();
		auto ui32ty = make_shared<IntTy<uint32_t>>();
		auto ui64ty = make_shared<IntTy<uint64_t>>();

		using the_tuple = tuple<TypePtr, TypePtr, Equality>;
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














