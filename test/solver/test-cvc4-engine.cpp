// Project
#include "../../src/solver/value.hpp"
#include "../../src/solver/type.hpp"
#include "../../src/solver/expr.hpp"
#include "../../src/solver/ismt-engine.hpp"
#include "../../src/solver/cvc4-engine.hpp"
#include "../../src/solver/expr-manager.hpp"

// Google Test
#include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>
#include <list>
#include <vector>

namespace solver {
	//TODO: global refactoring - make a template class
	class CVC4EngineTest : public ::testing::Test {
	public:
		void SetUp() {engine_ = new CVC4Engine();}
		void TearDown() {delete engine_;}
		ExprManagerPtr em_ = GetExprManager();
		CVC4Engine *engine_ = nullptr;
	};

	TEST_F(CVC4EngineTest, DISABLED_Constructor) {
		throw std::logic_error("not implemented");
	}

	TEST_F(CVC4EngineTest, DISABLED_Desctructor) {
		throw std::logic_error("not implemented");
	}

	TEST_F(CVC4EngineTest, DISABLED_CheckSat) {
		throw std::logic_error("not implemented");
	}

	//-------------------------------------------------------------------------
	// GetValue
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

	//-------------------------------------------------------------------------
	// Push-Pop

	TEST_F(CVC4EngineTest, DISABLED_Push_Pop__test1) {
		using namespace std;
		auto x = em_->MkVar("x", em_->MkIntTy<int32_t>());
		auto val = engine_->GetValue(x);
		// x is unbound variable
		ASSERT_EQ(nullptr, val);
	}

	TEST_F(CVC4EngineTest, DISABLED_Push_Pop__test2) {
		using namespace std;
		auto x_32 = em_->MkVar("x", em_->MkIntTy<int32_t>());
		auto x_16 = em_->MkVar("x", em_->MkIntTy<int16_t>());

		auto x_32_unbound = [&] {
			auto v1 = engine_->GetValue(x_32);
			ASSERT_EQ(nullptr, v1);
		};

		auto x_16_unbound = [&] {
			auto v2 = engine_->GetValue(x_16);
			ASSERT_EQ(nullptr, v2);
		};

		auto all_unbound = [&] () {
			x_32_unbound();
			x_16_unbound();
		};

		// level 1 - all variables are unbound
		all_unbound();
		engine_->Push(); {
			// level 2 - bind x_32
			all_unbound();
			auto orig_val = em_->MkIntVal<int32_t>(42);
			auto c42 = em_->MkConst(orig_val);
			auto binop = em_->MkBinOp(x_32, c42, Kind::EQ);
			engine_->Assert(binop);
			auto res_val = engine_->GetValue(x_32);
			EXPECT_EQ(orig_val, res_val);
			x_16_unbound();
		}
		engine_->Pop();
		// level 1 - all variables are unbound
		all_unbound();
		engine_->Push(); {
			// level 2 - bind x_16
		}
		engine_->Pop();
		// level 1 - all variables are unbound
		all_unbound();
	}

	//-------------------------------------------------------------------------
	// Prism testing

	TEST_F(CVC4EngineTest, Prism_nullptr) {
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

	template <typename T>
	void Prism_Var__helper (CVC4Engine *cvc4_engine, ExprManagerPtr expr_manager) {
		using namespace std;
		cvc4_engine->Push(); {
			auto name = string("x");
			auto ty = expr_manager->MkIntTy<T>();
			auto var = expr_manager->MkVar(name, ty);
			auto cvc4_var = cvc4_engine->Prism(var);
			//cout << "----------------\nTRACE: " << "original " << *var << " | cvc4 " << cvc4_var.toString() << " of type " << cvc4_var.getType().toString() << " of size " << static_cast<CVC4::BitVectorType>(cvc4_var.getType()).getSize() << endl;
			ASSERT_EQ(name, cvc4_var.toString());
			ASSERT_TRUE(cvc4_var.getType().isBitVector());
			ASSERT_EQ(sizeof(T)*8, static_cast<CVC4::BitVectorType>(cvc4_var.getType()).getSize());
		};
		cvc4_engine->Pop();
	}

	TEST_F(CVC4EngineTest, Prism_Var) {
		// (declare-const NAME (_ BitVec 32))
		auto cvc4engine = dynamic_cast<CVC4Engine*>(engine_);
		Prism_Var__helper<int8_t>(cvc4engine, em_);
		Prism_Var__helper<int16_t>(cvc4engine, em_);
		Prism_Var__helper<int32_t>(cvc4engine, em_);
		Prism_Var__helper<int64_t>(cvc4engine, em_);
		Prism_Var__helper<uint8_t>(cvc4engine, em_);
		Prism_Var__helper<uint16_t>(cvc4engine, em_);
		Prism_Var__helper<uint32_t>(cvc4engine, em_);
		Prism_Var__helper<uint64_t>(cvc4engine, em_);
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

	TEST_F(CVC4EngineTest, Prism_Const) {
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

	//TODO: Prism_BinOp testing - implement test case to check work with different Kind's

	template <typename T>
	void Prism_BinOp__helper (CVC4Engine *cvc4engine, ExprManagerPtr em) {
		using namespace std;
		using the_list = list<T>;

		auto checker = [&] (T val) {
			using namespace std;
			auto int_val = em->MkIntVal<T>(val);
			auto c = em->MkConst(int_val);
			auto int_ty = em->MkIntTy<T>();
			auto x = em->MkVar("x", int_ty);
			auto binop = em->MkBinOp(x, c, Kind::EQ);
			cvc4engine->Push(); {
				CVC4::Expr cvc4_expr = cvc4engine->Prism(binop);
				cout << "--------" << endl << binop->ToString() << " " << cvc4_expr.toString() << endl;
				// check op
				ASSERT_FALSE(cvc4_expr.isNull() or cvc4_expr.isVariable() or cvc4_expr.isConst());
				ASSERT_EQ(cvc4_expr.getKind(), CVC4::Kind::EQUAL);
				// check children
				std::vector<CVC4::Expr> children = cvc4_expr.getChildren();
				ASSERT_EQ(children.size(), 2);
				CVC4::Expr cvc4_x = children[0];
				CVC4::Expr cvc4_c = children[1];
				// check var
				ASSERT_EQ("x", cvc4_x.toString());
				CVC4::Type cvc4_x_ty = cvc4_x.getType();
				ASSERT_TRUE(cvc4_x_ty.isBitVector());
				CVC4::BitVectorType cvc4_x_btv_ty = static_cast<CVC4::BitVectorType>(cvc4_x_ty);
				ASSERT_EQ(sizeof(T)*8, cvc4_x_btv_ty.getSize());
				// check const
				CVC4::Type cvc4_c_ty = cvc4_c.getType();
				ASSERT_TRUE(cvc4_c_ty.isBitVector());
				CVC4::BitVectorType cvc4_c_btv_ty = static_cast<CVC4::BitVectorType>(cvc4_c_ty);
				ASSERT_EQ(sizeof(T)*8, cvc4_c_btv_ty.getSize());
				CVC4::BitVector cvc4_c_btv = cvc4_c.getConst<CVC4::BitVector>();
				CVC4::Integer cvc4_c_integer = cvc4_c_btv.toInteger();
				auto actual_raw_ulong = cvc4_c_integer.getUnsignedLong();
				cout << "sizeof actual ulong : " << sizeof(actual_raw_ulong) << endl;
				auto basic_int_val = dynamic_pointer_cast<BasicInt>(int_val);
				uint64_t expected_raw_ulong = basic_int_val->GetUInt64();
				ASSERT_EQ(expected_raw_ulong, actual_raw_ulong);
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

	TEST_F(CVC4EngineTest, Prism_BinOp) {
		auto cvc4engine = dynamic_cast<CVC4Engine*>(engine_);
		/*Prism_BinOp__helper<int8_t>(cvc4engine, em_);
		Prism_BinOp__helper<int16_t>(cvc4engine, em_);*/
		Prism_BinOp__helper<int32_t>(cvc4engine, em_);
		Prism_BinOp__helper<int64_t>(cvc4engine, em_);
		/*Prism_BinOp__helper<uint8_t>(cvc4engine, em_);
		Prism_BinOp__helper<uint16_t>(cvc4engine, em_);
		Prism_BinOp__helper<uint32_t>(cvc4engine, em_);*/
		Prism_BinOp__helper<uint64_t>(cvc4engine, em_);
	}






	//-------------------------------------------------------------------------
	// CVC4 Internals:
	TEST_F(CVC4EngineTest, DISABLED_CVC4ExprManagerBug_part1) {
		// No error - normal behavior
		CVC4::ExprManager cvc4em;
		CVC4::Type btv_ty1 = cvc4em.mkBitVectorType(32);
		CVC4::Type btv_ty2 = cvc4em.mkBitVectorType(32);
		ASSERT_EQ(btv_ty1, btv_ty2);
	}

	TEST_F(CVC4EngineTest, DISABLED_CVC4ExprManagerBug_part2) {
		// Error - 2 structural equivalent objects are equal
		CVC4::ExprManager cvc4em1;
		CVC4::ExprManager cvc4em2;
		CVC4::Type btv_ty1 = cvc4em1.mkBitVectorType(32);
		CVC4::Type btv_ty2 = cvc4em2.mkBitVectorType(32);
		ASSERT_EQ(btv_ty1, btv_ty2);
	}

	TEST_F(CVC4EngineTest, DISABLED_CVC4ExprManagerScopes) {
		using namespace std;
		CVC4::ExprManager em;
		CVC4::SmtEngine engine(&em);
		CVC4::SymbolTable symbol_table;
		engine.setOption("incremental", CVC4::SExpr("true"));
		engine.setOption("produce-models", CVC4::SExpr("true"));
		engine.setOption("rewrite-divk", CVC4::SExpr("true"));
		auto btv32_ty = em.mkBitVectorType(32);
		auto btv16_ty = em.mkBitVectorType(16);
		auto x1 = em.mkVar("x", btv32_ty);
		auto x2 = em.mkVar("x", btv16_ty);
		symbol_table.pushScope(); {
			cout << "level " << symbol_table.getLevel() << endl;
			cout << "is bound x " << symbol_table.isBound("x") << endl;
			symbol_table.bind("x", x1);
			cout << "x 32 bound " << endl;
			cout << "lookup x: " << symbol_table.lookup("x") << symbol_table.lookup("x").getType() << endl;
			symbol_table.pushScope(); {
				cout << "level " << symbol_table.getLevel() << endl;
				cout << "is bound x " << symbol_table.isBound("x") << endl;
				symbol_table.bind("x", x2);
				cout << "x 16 bound " << endl;
				cout << "lookup x: " << symbol_table.lookup("x") << symbol_table.lookup("x").getType() << endl;
			}
			symbol_table.popScope();
			cout << "level " << symbol_table.getLevel() << endl;
			cout << "lookup x: " << symbol_table.lookup("x") << symbol_table.lookup("x").getType() << endl;
		}
		symbol_table.popScope();
	}
}













