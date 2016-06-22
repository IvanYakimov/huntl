// Project
#include "../../src/solver/value.hpp"
#include "../../src/solver/type.hpp"
#include "../../src/solver/expr.hpp"
#include "../../src/solver/ismt-engine.hpp"
#include "../../src/solver/cvc4-engine.hpp"
#include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>
#include <list>
#include <vector>
#include "../../src/solver/object-builder.hpp"
#include "../../src/solver/object-builder-helper.hpp"

namespace solver {
	//TODO: global refactoring - make a template class
	class CVC4EngineTest : public ::testing::Test {
	public:
		void SetUp() {engine_ = new CVC4Engine();}
		void TearDown() {
			try { delete engine_; } catch (Exception &ex) {;}
		}
		ObjectBuilderPtr em_ = ObjectBuilder::Get();
		CVC4Engine *engine_ = nullptr;
	};

	//-------------------------------------------------------------------------
	// Assert
	TEST_F(CVC4EngineTest, Assert__invalid_type) {

		auto x = V<int32_t>("x");
		try {
			engine_->Assert(x);
			FAIL();
		}
		catch (TypeCheckingException &ex) {}
	}

	//-------------------------------------------------------------------------
	// GetValue
	TEST_F(CVC4EngineTest, GetValue__unbound_var) {

		auto x = V<int32_t>("x");
		ASSERT_EQ(engine_->CheckSat(), Sat::SAT);
		try {
			engine_->GetValue(x); 	// x is unbound
			FAIL();
		}
		catch (BindingException &ex) {}
	}

	TEST_F(CVC4EngineTest, GetValue__invalid_type) {

		auto x = V<int32_t>("x");
		auto zero = C<int32_t>(0);
		auto expr = Equal(x, zero);
		engine_->Assert(expr);
		ASSERT_EQ(Sat::SAT, engine_->CheckSat());
		try {
			auto bad_x = V<int16_t>("x");
			engine_->GetValue(bad_x);
			FAIL();
		}
		catch (TypeCheckingException &ex) {}
	}

	TEST_F(CVC4EngineTest, GetValue__with_negative_sat_checking_result) {

		auto x = V<int32_t>("x");
		auto zero = C<int32_t>(0);
		auto x_eq_zero = Equal(x, zero);
		auto x_ne_zero = Distinct(x, zero);
		engine_->Assert(x_eq_zero);
		engine_->Assert(x_ne_zero);
		auto sat = engine_->CheckSat();
		ASSERT_EQ(Sat::UNSAT, sat);
		try {
			engine_->GetValue(x);	// try to get value with unsat stack
			FAIL();
		}
		catch (ModelException &ex) {}
	}

	TEST_F(CVC4EngineTest, GetValue__binop_is_unimplemented) {

		auto x = V<int32_t>("x");
		auto zero = C<int32_t>(0);
		auto x_ne_zero = Distinct(x, zero);
		engine_->Assert(x_ne_zero);
		try {
			engine_->GetValue(x_ne_zero); // not a variable
			FAIL();
		}
		catch (ImplementationException &ex) {}
	}

	TEST_F(CVC4EngineTest, GetValue__constan_is_unimplemented) {

		ASSERT_EQ(engine_->CheckSat(), Sat::SAT);
		try {
			engine_->GetValue(C<int32_t>(1));
		}
		catch (ImplementationException &ex) {}
	}

	template <typename T>
	void GetValue__helper (CVC4Engine *cvc4engine, ObjectBuilderPtr em) {
		using namespace std;
		using the_list = list<T>;

		auto checker = [&] (T val) {
			auto val_obj = em->MkIntVal<T>(val);
			auto c = em->MkConst(val_obj);
			auto ty = em->MkIntTy<T>();
			auto x = em->MkVar("x", ty);
			auto binop = em->MkDoubleNode(x, c, Kind::EQUAL);

			cvc4engine->Push(); {
				cvc4engine->Assert(binop);
				if (cvc4engine->CheckSat() == Sat::SAT) {
					auto obtained = cvc4engine->GetValue(x);
					//cout << *val_obj << " -> "<< *obtained << endl;
					ASSERT_EQ(*val_obj, *obtained);
				}
				else
					FAIL();
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

	TEST_F(CVC4EngineTest, GetValue_parametrized) {
		// (declare-const x (_ BitVec 32))
		// (assert (= x VAL))
		// (check-sat)
		// (get-value (x))
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

	TEST_F(CVC4EngineTest, Push_Pop_1) {
		using namespace std;
		auto x = em_->MkVar("x", em_->MkIntTy<int32_t>());
		try {
			auto val = engine_->GetValue(x);
			FAIL();
		} // x is unbound
		catch (BindingException &ex) {}

	}

	TEST_F(CVC4EngineTest, Push_Pop_2) {
		using namespace std;
		auto x_32 = em_->MkVar("x", em_->MkIntTy<int32_t>());

		auto x_32_unbound = [&] {
			try {
				auto val = engine_->GetValue(x_32);
				FAIL();
			}
			catch (BindingException &ex) {}
		};

		// level 1 - all variables are unbound
		x_32_unbound();
		engine_->Push(); {
			// level 2 - bind x_32
			x_32_unbound();
			auto orig_val = em_->MkIntVal<int32_t>(42);
			auto c42 = em_->MkConst(orig_val);
			auto binop = em_->MkDoubleNode(x_32, c42, Kind::EQUAL);
			engine_->Assert(binop);
			if (engine_->CheckSat() == Sat::SAT) {
				auto res_val = engine_->GetValue(x_32);
				EXPECT_EQ(*orig_val, *res_val);
			}
			else FAIL();
		}
		engine_->Pop();
		// level 1 - all variables are unbound
		x_32_unbound();
	}

	TEST_F(CVC4EngineTest, Pop) {
		bool thrown = false;
		try {
			engine_->Pop(); // scope level 1 -> 0
			engine_->Pop(); // failure
			FAIL();
		}
		catch (solver::ScopeException &ex) {
			thrown = true;
		}
		ASSERT_TRUE(thrown);
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
	void Prism_Var__helper (CVC4Engine *cvc4_engine, ObjectBuilderPtr expr_manager) {
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
	void Prism_Const__helper (CVC4Engine *cvc4engine, ObjectBuilderPtr em) {
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
			ValuePtr re_conv =  em->MkIntVal(dynamic_pointer_cast<BasicIntVal>(val_obj)->IsSigned(), from_size_t(sizeof(T)), ulval);
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

	//TODO: Prism_BinOp testing - implement test case to check work with different Kinds
	template <typename T>
	void Prism_BinOp__helper (CVC4Engine *cvc4engine, ObjectBuilderPtr em) {
		using namespace std;
		using the_list = list<T>;

		auto checker = [&] (T val) {
			using namespace std;
			auto int_val = em->MkIntVal<T>(val);
			auto c = em->MkConst(int_val);
			auto int_ty = em->MkIntTy<T>();
			auto x = em->MkVar("x", int_ty);
			auto binop = em->MkDoubleNode(x, c, Kind::EQUAL);
			cvc4engine->Push(); {
				CVC4::Expr cvc4_expr = cvc4engine->Prism(binop);
				//cout << "--------" << endl << binop->ToString() << " " << cvc4_expr.toString() << endl;
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
				//cout << "sizeof actual ulong : " << sizeof(actual_raw_ulong) << endl;
				auto basic_int_val = dynamic_pointer_cast<BasicIntVal>(int_val);
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
		Prism_BinOp__helper<int8_t>(cvc4engine, em_);
		Prism_BinOp__helper<int16_t>(cvc4engine, em_);
		Prism_BinOp__helper<int32_t>(cvc4engine, em_);
		Prism_BinOp__helper<int64_t>(cvc4engine, em_);
		Prism_BinOp__helper<uint8_t>(cvc4engine, em_);
		Prism_BinOp__helper<uint16_t>(cvc4engine, em_);
		Prism_BinOp__helper<uint32_t>(cvc4engine, em_);
		Prism_BinOp__helper<uint64_t>(cvc4engine, em_);
	}

	//-------------------------------------------------------------------------
	// Basic operations testing
	TEST_F(CVC4EngineTest, helpers_test) {
		using namespace std;

		using the_tuple = tuple<function<ExprPtr(ExprPtr, ExprPtr)>, Kind>;
		using the_list = list<the_tuple>;
		auto checker = [&] (the_tuple tpl) {
			auto f = get<0>(tpl);
			auto k = get<1>(tpl);
			auto l = V<int32_t>("x");
			auto r = C<int32_t>(42);
			auto act = f(l, r);
			auto exp = ObjectBuilder::Get()->MkDoubleNode(l, r, k);
			ASSERT_EQ(*exp, *act);
		};

		the_list val_list = {
				make_tuple(Add, Kind::ADD),
				make_tuple(Sub, Kind::SUB),
				make_tuple(Mul, Kind::MUL),
				make_tuple(SDiv, Kind::SDIV),
				make_tuple(SRem, Kind::SREM),
				make_tuple(UDiv, Kind::UDIV),
				make_tuple(URem, Kind::UREM),
				make_tuple(Shl, Kind::SHL),
				make_tuple(LShr, Kind::LSHR),
				make_tuple(AShr, Kind::ASHR),
				make_tuple(And, Kind::AND),
				make_tuple(Or, Kind::OR),
				make_tuple(Xor, Kind::XOR),
				make_tuple(Equal, Kind::EQUAL),
				make_tuple(Distinct, Kind::DISTINCT),
				make_tuple(UGt, Kind::UGT),
				make_tuple(UGe, Kind::UGE),
				make_tuple(ULt, Kind::ULT),
				make_tuple(ULe, Kind::ULE),
				make_tuple(SGt, Kind::SGT),
				make_tuple(SGe, Kind::SGE),
				make_tuple(ULt, Kind::ULT),
				make_tuple(ULe, Kind::ULE)
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}

	template <typename T>
	void arithmetic_helper(ISMTEngine* engine) {
		using namespace std;

		using native = function<T(T,T)>;

		native _add = [] (T a, T b) -> T {return a + b;};
		native _sub = [] (T a, T b) -> T {return a - b;};
		native _mul	= [] (T a, T b) -> T {return a * b;};
		native _sdiv = [] (T a, T b) -> T {return a / b;};
		native _srem = [] (T a, T b) -> T {return a % b;};
		native _udiv = [] (T a, T b) -> T {return a / b;};
		native _urem = [] (T a, T b) -> T {return a % b;};
		native _shl = [] (T a, T b) -> T {return a << b;};
		native _shr = [] (T a, T b) -> T {return a >> b;};
		native _or = [] (T a, T b) -> T {return a | b;};
		native _and = [] (T a, T b) -> T {return a & b;};
		native _xor = [] (T a, T b) -> T {return a ^ b;};

		using the_context = tuple<Func, native, string>;
		using the_tuple = tuple<T, T, T, the_context>;
		using the_list = list<the_tuple>;

		auto _add_cnxt = make_tuple(Add, _add, "+");
		auto _sub_cnxt = make_tuple(Sub, _sub, "-");
		auto _mul_cnxt = make_tuple(Mul, _mul, "*");
		auto _sdiv_cnxt = make_tuple(SDiv, _sdiv, "`sdiv`");
		auto _srem_cnxt = make_tuple(SRem, _srem, "`srem`");
		auto _udiv_cnxt = make_tuple(UDiv, _udiv, "`udiv`");
		auto _urem_cnxt = make_tuple(URem, _urem, "`urem`");
		auto _shl_cnxt = make_tuple(Shl, _shl, "`shl`");
		auto _ashr_cnxt = make_tuple(AShr, _shr, "`ashr`");
		auto _lshr_cnxt = make_tuple(LShr, _shr, "`lshr`");
		auto _or_cnxt = make_tuple(Or, _or, "`or`");
		auto _and_cnxt = make_tuple(And, _and, "`and`");
		auto _xor_cnxt = make_tuple(Xor, _xor, "`xor`");

		auto checker = [&] (the_tuple tpl) {
			T raw_a = get<0>(tpl);
			T raw_b = get<1>(tpl);
			T raw_c = get<2>(tpl);
			the_context context = get<3>(tpl);
			Func f = get<0>(context);
			native g = get<1>(context);
			string op = get<2>(context);
			auto a = C<T>(raw_a);
			auto b = C<T>(raw_b);
			auto c = C<T>(raw_c);
			auto fab = f(a,b);
			auto from_native = C<T>(g(raw_a,raw_b));
			auto expr = Equal(V<T>("x"), fab);
			engine->Push(); {
				engine->Assert(expr);
				if(engine->CheckSat() == Sat::SAT) {
					auto actual = engine->GetValue(V<T>("x"));
					auto expected = dynamic_pointer_cast<Const>(c)->GetValue();
					auto exp_native = dynamic_pointer_cast<Const>(from_native)->GetValue();

					//Verbose <
					if (*expected != *actual)
					{
						engine->Pop();
						auto get_bitwise = [] (T arg) -> string {
							return bitset<sizeof(T)*8>(arg).to_string();
						};

						cout << "---------------------------------------" << endl;
						auto raw_printer = [&] (T val) -> string {
							if (val == numeric_limits<T>::max())
								return "max";
							else if (val == numeric_limits<T>::min())
								return "min";
							else
								return std::to_string(val);
						};
						cout << raw_printer(raw_a) << " " << op << " " << raw_printer(raw_b) << " = " << raw_printer(raw_c) << endl;
						cout << endl << get_bitwise(raw_a) << endl << op << endl << get_bitwise(raw_b) << endl << "=" << endl << get_bitwise(raw_c) << endl;
					}
					// >

					ASSERT_EQ(*expected, *actual);
					ASSERT_EQ(*exp_native, *actual);
				}
				else
					FAIL();
			}
			engine->Pop();
		};

		T max = numeric_limits<T>::max();
		T min = numeric_limits<T>::min();

		the_list main_list, sign_list, unsign_list;

		main_list = {

		};

		if (numeric_limits<T>::is_signed) {
			sign_list = {
					// ADD
					make_tuple(8,		2,		10,		_add_cnxt),
					make_tuple(8,		-2,		6,		_add_cnxt),
					make_tuple(max, 	max, 	-2, 	_add_cnxt),
					make_tuple(max, 	1, 		min, 	_add_cnxt),
					make_tuple(max,		min,	-1,		_add_cnxt),
					make_tuple(min, 	min, 	0, 		_add_cnxt),
					make_tuple(0, 		1, 		1, 		_add_cnxt),
					// SUB
					make_tuple(8,		2,		6,		_sub_cnxt),
					make_tuple(8,		-2,		10,		_sub_cnxt),
					make_tuple(max,		max, 	0,		_sub_cnxt),
					make_tuple(max,		min,	-1,		_sub_cnxt),
					make_tuple(min, 	max,	1,		_sub_cnxt),
					make_tuple(min,		min,	0,		_sub_cnxt),
					make_tuple(0,		max,	max+2,	_sub_cnxt),
					make_tuple(0, 		min, 	min,	_sub_cnxt),
					make_tuple(1, 		0, 		1,		_sub_cnxt),
					make_tuple(0,		1,		-1,		_sub_cnxt),
					// MUL
					make_tuple(8,		2,		16,		_mul_cnxt),
					make_tuple(8,		-2,		-16,	_mul_cnxt),
					make_tuple(0,		1, 		0,		_mul_cnxt),
					make_tuple(1,		1, 		1, 		_mul_cnxt),
					make_tuple(1,		2,		2,		_mul_cnxt),
					make_tuple(1,		max,	max,	_mul_cnxt),
					make_tuple(1,		min,	min,	_mul_cnxt),
					make_tuple(max,		max,	1,		_mul_cnxt),
					make_tuple(min,		min,	0,		_mul_cnxt),
					// SDIV
					make_tuple(8,		2,		4,		_sdiv_cnxt),
					make_tuple(8,		-2,		-4,		_sdiv_cnxt),
					make_tuple(0,		1,		0,		_sdiv_cnxt),
					make_tuple(0,		-1,		0,		_sdiv_cnxt),
					make_tuple(max,		max,	1,		_sdiv_cnxt),
					make_tuple(min, 	min,	1,		_sdiv_cnxt),
					// SREM
					make_tuple(8,		3,		2,		_sdiv_cnxt),
					make_tuple(8,		-3,		-2,		_sdiv_cnxt),
					// SHL
					make_tuple(0,		1,		0,		_shl_cnxt),
					make_tuple(1,		1,		2,		_shl_cnxt),
					make_tuple(2,		2,		8,		_shl_cnxt),
					make_tuple(max,		1,		-2,		_shl_cnxt),
					make_tuple(min,		1,		0, 		_shl_cnxt),
					// ASHR
					make_tuple(0,		1,		0,		_ashr_cnxt),
					make_tuple(1,		1,		0,		_ashr_cnxt),
					make_tuple(max,		1,		max/2,	_ashr_cnxt),
					make_tuple(min,		1,		min/2,	_ashr_cnxt),
					// OR
					make_tuple(0,		0,		0,		_or_cnxt),
					make_tuple(1,		0,		1,		_or_cnxt),
					make_tuple(1,		1,		1,		_or_cnxt),
					make_tuple(max,		0,		max,	_or_cnxt),
					make_tuple(min,		0,		min,	_or_cnxt),
					// AND
					make_tuple(0,		0,		0,		_and_cnxt),
					make_tuple(1,		0,		0,		_and_cnxt),
					make_tuple(1,		1,		1,		_and_cnxt),
					make_tuple(max,		0,		0,		_and_cnxt),
					make_tuple(min,		0,		0,		_and_cnxt),
					// XOR
					make_tuple(0,		0,		0,		_xor_cnxt),
					make_tuple(0,		1,		1,		_xor_cnxt),
					make_tuple(1,		1,		0,		_xor_cnxt),
					make_tuple(max,		0,		max,	_xor_cnxt),
					make_tuple(max,		-1,		min,	_xor_cnxt),
					make_tuple(min,		-1,		max,	_xor_cnxt)
			};
		}
		else {
			unsign_list = {
				// ADD
				make_tuple(8,		2,		10,		_add_cnxt),
				make_tuple(8,		-2,		6,		_add_cnxt),
				make_tuple(max, 	max, 	max-1, 	_add_cnxt),
				make_tuple(max, 	1, 		min, 	_add_cnxt),
				make_tuple(max,		min,	max,	_add_cnxt),
				make_tuple(min, 	min, 	0, 		_add_cnxt),
				make_tuple(0, 		1, 		1, 		_add_cnxt),
				// SUB
				make_tuple(8,		2,		6,		_sub_cnxt),
				make_tuple(8,		-2,		10,		_sub_cnxt),
				make_tuple(max,		max, 	0,		_sub_cnxt),
				make_tuple(max,		min,	max,	_sub_cnxt),
				make_tuple(min, 	max,	1,		_sub_cnxt),
				make_tuple(min,		min,	0,		_sub_cnxt),
				make_tuple(0,		max,	1,		_sub_cnxt),
				make_tuple(0, 		min, 	min,	_sub_cnxt),
				make_tuple(1, 		0, 		1,		_sub_cnxt),
				make_tuple(0,		1,		max,	_sub_cnxt),
				// MUL
				make_tuple(8,		2,		16,		_mul_cnxt),
				make_tuple(0,		1, 		0,		_mul_cnxt),
				make_tuple(1,		1, 		1, 		_mul_cnxt),
				make_tuple(1,		2,		2,		_mul_cnxt),
				make_tuple(1,		max,	max,	_mul_cnxt),
				make_tuple(1,		min,	min,	_mul_cnxt),
				make_tuple(max,		max,	1,		_mul_cnxt),
				make_tuple(min,		min,	0,		_mul_cnxt),
				// UDIV
				make_tuple(8,		2,		4,		_udiv_cnxt),
				make_tuple(0,		1,		0,		_udiv_cnxt),
				make_tuple(max,		max,	1,		_udiv_cnxt),
				// UREM
				make_tuple(8,		3,		2,		_urem_cnxt),
				// SHL
				make_tuple(1,		1,		2,		_shl_cnxt),
				make_tuple(2,		2,		8,		_shl_cnxt),
				make_tuple(min,		1,		0,		_shl_cnxt),
				make_tuple(max,		1,		max-1,	_shl_cnxt),
				// LSHR
				make_tuple(1,		1,		0,		_lshr_cnxt),
				make_tuple(min,		1,		0,		_lshr_cnxt),
				make_tuple(max,		1,		max/2,	_lshr_cnxt),
				// OR
				make_tuple(0,		0,		0,		_or_cnxt),
				make_tuple(1,		0,		1,		_or_cnxt),
				make_tuple(1,		1,		1,		_or_cnxt),
				make_tuple(max,		0,		max,	_or_cnxt),
				make_tuple(min,		0,		min,	_or_cnxt),
				// AND
				make_tuple(0,		0,		0,		_and_cnxt),
				make_tuple(1,		0,		0,		_and_cnxt),
				make_tuple(1,		1,		1,		_and_cnxt),
				make_tuple(max,		0,		0,		_and_cnxt),
				make_tuple(min,		0,		0,		_and_cnxt),
				// XOR
				make_tuple(0,		0,		0,		_xor_cnxt),
				make_tuple(0,		1,		1,		_xor_cnxt),
				make_tuple(1,		1,		0,		_xor_cnxt),
				make_tuple(max,		0,		max,	_xor_cnxt),
				make_tuple(max,		max,	min,	_xor_cnxt),
				make_tuple(min,		max,	max,	_xor_cnxt)
			};
		}

		if (numeric_limits<T>::is_signed)
			main_list.splice(main_list.end(), sign_list);
		else
			main_list.splice(main_list.end(), unsign_list);

		for_each(main_list.begin(), main_list.end(), checker);
	}

	TEST_F(CVC4EngineTest, arithmetic) {
		using namespace std;
		ISMTEngine *engine_ptr = dynamic_cast<ISMTEngine*>(engine_);
		arithmetic_helper<int8_t>(engine_ptr);
		arithmetic_helper<int16_t>(engine_ptr);
		arithmetic_helper<int32_t>(engine_ptr);
		arithmetic_helper<int64_t>(engine_ptr);
		arithmetic_helper<uint8_t>(engine_ptr);
		arithmetic_helper<uint16_t>(engine_ptr);
		arithmetic_helper<uint32_t>(engine_ptr);
		arithmetic_helper<uint64_t>(engine_ptr);
	}

	template <typename T>
	void comparisons_helper(ISMTEngine* engine) {
		using namespace std;

		using native = function<bool(T,T)>;

		using the_context = tuple<Func, native, string>;
		using the_tuple = tuple<the_context>;
		using the_list = list<the_tuple>;

		native _equal = [] (T a, T b) -> bool {return a == b;};
		native _distinct = [] (T a, T b) -> bool {return a != b;};
		native _gt = [] (T a, T b) -> T {return a > b;};
		native _ge = [] (T a, T b) -> T {return a >= b;};
		native _lt = [] (T a, T b) -> T {return a < b;};
		native _le = [] (T a, T b) -> T {return a <= b;};

		auto _equal_cnxt = make_tuple(Equal, _equal, "=");
		auto _distinct_cnxt = make_tuple(Distinct, _distinct, "`distinct`");
		auto _sgt_cnxt = make_tuple(SGt, _gt, "`sgt`");
		auto _sge_cnxt = make_tuple(SGe, _ge, "`sge`");
		auto _slt_cnxt = make_tuple(SLt, _lt, "`slt`");
		auto _sle_cnxt = make_tuple(SLe, _le, "`sle`");
		auto _ugt_cnxt = make_tuple(UGt, _gt, "`ugt`");
		auto _uge_cnxt = make_tuple(UGe, _ge, "`uge`");
		auto _ult_cnxt = make_tuple(ULt, _lt, "`ult`");
		auto _ule_cnxt = make_tuple(ULe, _le, "`ule`");

		auto checker = [&] (the_tuple tpl) {
			auto cnxt = get<0>(tpl);
			Func f = get<0>(cnxt);
			native ntv_f = get<1>(cnxt);
			string f_name = get<2>(cnxt);
			ExprPtr x = V<T>("x");
			ExprPtr y = V<T>("y");
			ExprPtr x_op_y = f(x, y);
			engine->Push(); {
				engine->Assert(x_op_y);
				if (engine->CheckSat() == Sat::SAT) {
					ValuePtr x_val = engine->GetValue(x);
					ValuePtr y_val = engine->GetValue(y);
					T raw_x_val = dynamic_pointer_cast<IntVal<T>>(x_val)->GetVal();
					T raw_y_val = dynamic_pointer_cast<IntVal<T>>(y_val)->GetVal();
					ASSERT_TRUE(ntv_f(raw_x_val, raw_y_val));
					//< Verbose
					/*
					{
						cout << "-------------------------------" << endl;
						cout << "x " << f_name << " y has a model: " << endl;
						cout << *x_val << " | " << *y_val << endl;
					}
					//> */
				}
				else
					FAIL();
			}
			engine->Pop();
		};

		the_list main_list, sign_list, unsign_list;
		main_list = {
			make_tuple(_equal_cnxt),
			make_tuple(_distinct_cnxt)
		};

		if (numeric_limits<T>::is_signed) {
			sign_list = {
				make_tuple(_sgt_cnxt),
				make_tuple(_sge_cnxt),
				make_tuple(_slt_cnxt),
				make_tuple(_sle_cnxt)
			};
		}
		else {
			unsign_list = {
				make_tuple(_ugt_cnxt),
				make_tuple(_uge_cnxt),
				make_tuple(_ult_cnxt),
				make_tuple(_ule_cnxt)
			};
		}

		if (numeric_limits<T>::is_signed)
			main_list.splice(main_list.end(), sign_list);
		else
			main_list.splice(main_list.end(), unsign_list);

		for_each(main_list.begin(), main_list.end(), checker);
	}

	TEST_F(CVC4EngineTest, comparisons) {
		using namespace std;
		ISMTEngine *engine_ptr = dynamic_cast<ISMTEngine*>(engine_);
		comparisons_helper<int8_t>(engine_ptr);
		comparisons_helper<int16_t>(engine_ptr);
		comparisons_helper<int32_t>(engine_ptr);
		comparisons_helper<int64_t>(engine_ptr);
		comparisons_helper<uint8_t>(engine_ptr);
		comparisons_helper<uint16_t>(engine_ptr);
		comparisons_helper<uint32_t>(engine_ptr);
		comparisons_helper<uint64_t>(engine_ptr);
	}

	TEST_F(CVC4EngineTest, DISABLED_division_by_zero) {

		auto x = V<int32_t>("x");
		auto a = C<int32_t>(1);
		auto b = C<int32_t>(0);
		auto expr = Equal(x, SDiv(a, b));
		engine_->Assert(expr);
		engine_->CheckSat();
		auto val = engine_->GetValue(x);
		std::cout << *val << std::endl;
	}
}













