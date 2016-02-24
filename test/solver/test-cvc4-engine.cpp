// Project
# include "../../src/solver/expr.hpp"
# include "../../src/solver/ismt-engine.hpp"
# include "../../src/solver/cvc4-engine.hpp"
#include "../../src/solver/expr-manager.hpp"

// Google Test
# include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>
#include <list>

namespace solver {
	//TODO: global refactoring - make a template class
	class CVC4EngineTest : public ::testing::Test {
	public:
		void SetUp() {engine_ = new CVC4Engine();}
		void TearDown() {delete engine_;}
		ExprManagerPtr em_ = GetExprManager();
		CVC4Engine *engine_ = nullptr;
	};

	//-------------------------------------------------------------------------
	// Prism testing

	TEST_F(CVC4EngineTest, DISABLED_Prism_nullptr) {
		bool nlp_ex = false;
		try {
			ExprPtr nlp = nullptr;
			engine_->Prism(nlp);
		}
		catch (std::logic_error &e) {
			nlp_ex = true;
		}
		ASSERT_TRUE(nlp_ex);
	}

	TEST_F(CVC4EngineTest, CVC4ExprManagerBug_part1) {
		// No error - normal behavior
		CVC4::ExprManager cvc4em;
		CVC4::Type btv_ty1 = cvc4em.mkBitVectorType(32);
		CVC4::Type btv_ty2 = cvc4em.mkBitVectorType(32);
		ASSERT_EQ(btv_ty1, btv_ty2);
	}

	TEST_F(CVC4EngineTest, CVC4ExprManagerBug_part2) {
		// Error - 2 structural equivalent objects are equal
		CVC4::ExprManager cvc4em1;
		CVC4::ExprManager cvc4em2;
		CVC4::Type btv_ty1 = cvc4em1.mkBitVectorType(32);
		CVC4::Type btv_ty2 = cvc4em2.mkBitVectorType(32);
		ASSERT_EQ(btv_ty1, btv_ty2);
	}

	template <typename T>
	void Prism_Var__helper (CVC4Engine *cvc4engine_, ExprManagerPtr em_, CVC4::ExprManager &cvc4em) {
		std::string name = "x";
		auto ty = em_->MkIntTy<T>();
		ExprPtr var = em_->MkVar(name, ty);
		CVC4::Expr cvc4_var = cvc4engine_->Prism(var);
		ASSERT_EQ(name, cvc4_var.toString());
		ASSERT_TRUE(cvc4_var.getType().isBitVector());
	}

	TEST_F(CVC4EngineTest, Prism_Var) {
		// (declare-const NAME (_ BitVec 32))
		auto cvc4engine = dynamic_cast<CVC4Engine*>(engine_);
		auto cvc4em = cvc4engine->expr_manager_;
		Prism_Var__helper<int8_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<int16_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<int32_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<int64_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<uint8_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<uint16_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<uint32_t>(cvc4engine, em_, cvc4em);
		Prism_Var__helper<uint64_t>(cvc4engine, em_, cvc4em);
	}

	template <typename T>
	void Prism_Const__helper (CVC4Engine *cvc4engine, ExprManagerPtr em) {
		using namespace std;
		using the_list = list<T>;

		auto checker = [&] (T val) {
			auto val_obj = em->MkIntVal<T>(val);
			auto x = em->MkConst(val_obj);
			cvc4engine->Push();
			CVC4::Expr expr = cvc4engine->Prism(x);
			CVC4::BitVector cvc4_btv = expr.getConst<CVC4::BitVector>();
			CVC4::Integer cvc4_int = cvc4_btv.toInteger();
			uint64_t ulval = cvc4_int.getUnsignedLong();
			ValuePtr re_conv =  em->MkIntVal(dynamic_pointer_cast<BasicInt>(val_obj)->IsSigned(), width::from_size_t(sizeof(T)), ulval);
			EXPECT_EQ(*val_obj, *re_conv);
			cvc4engine->Pop();
		};

		the_list val_list = {
				numeric_limits<T>::max(),
				numeric_limits<T>::min(),
				0,
				42,
		};

		if (numeric_limits<T>::is_signed) val_list.push_back(-42);

		for_each (val_list.begin(), val_list.end(), checker);
	}

	//TODO: refactoring - combinarorial testing
	TEST_F(CVC4EngineTest, DISABLED_Prism_Const) {
		// (display (_ bv32 VAL))
		auto cvc4engine = dynamic_cast<CVC4Engine*>(engine_);
		Prism_Const__helper<int8_t>(cvc4engine, em_);
		Prism_Const__helper<int16_t>(cvc4engine, em_);
		Prism_Const__helper<int32_t>(cvc4engine, em_);
		Prism_Const__helper<int64_t>(cvc4engine, em_);
		Prism_Const__helper<uint8_t>(cvc4engine, em_);
		Prism_Const__helper<uint16_t>(cvc4engine, em_);
		Prism_Const__helper<uint32_t>(cvc4engine, em_);
		Prism_Const__helper<uint64_t>(cvc4engine, em_);
	}

	template <typename T>
	void GetValue__helper (CVC4Engine *cvc4engine, ExprManagerPtr em) {
		using namespace std;
		using the_list = list<T>;

		auto checker = [&] (T val) {
			auto val_obj = em->MkIntVal<T>(val);
			auto c = em->MkConst(val_obj);
			auto ty = em->MkIntTy<T>();
			auto x = em->MkVar("x", ty);
			auto binop = em->MkBinOp(x, c, Kind::EQ);

			cvc4engine->Push(); {
				cvc4engine->Assert(binop);
				auto obtained = cvc4engine->GetValue(x);
				cout << *obtained << endl;
			}
			cvc4engine->Pop();
		};

		the_list val_list = {
				numeric_limits<T>::max(),
				numeric_limits<T>::min(),
				0,
				42,
		};

		if (numeric_limits<T>::is_signed) val_list.push_back(-42);

		for_each (val_list.begin(), val_list.end(), checker);
	}

	TEST_F(CVC4EngineTest, DISABLED_GetValue) {
		// (declare-const x (_ BitVec 32))
		// (assert (= x VAL))
		// (check-sat)
		// (get-value (x))
		//TODO:
		auto cvc4engine = dynamic_cast<CVC4Engine*>(engine_);
		GetValue__helper<int8_t>(cvc4engine, em_);
		GetValue__helper<int16_t>(cvc4engine, em_);
		GetValue__helper<int32_t>(cvc4engine, em_);
		GetValue__helper<int64_t>(cvc4engine, em_);
		GetValue__helper<uint8_t>(cvc4engine, em_);
		GetValue__helper<uint16_t>(cvc4engine, em_);
		GetValue__helper<uint32_t>(cvc4engine, em_);
		GetValue__helper<uint64_t>(cvc4engine, em_);
	}
}













