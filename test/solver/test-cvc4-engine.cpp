// Project
# include "../../src/solver/expr.hpp"
# include "../../src/solver/ismt-engine.hpp"
# include "../../src/solver/cvc4-engine.hpp"

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
	SharedExpr mkvar(std::string name) {ExprFactory::MkVar(name);}
	void SetUp() {engine_ = new CVC4Engine();}
	void TearDown() {delete engine_;}
	CVC4Engine *Engine() const { return engine_; }
private:
	CVC4Engine *engine_ = nullptr;
};

template<typename T>
void ability_test() {
	using namespace ::CVC4;
	using Expr = ::CVC4::Expr;
	using std::cout;
	using std::endl;
	//std::cout << "T: " << typeid(T).name() << " width = " << width << endl;
	ExprManager em;
	SmtEngine smt(&em);
	smt.setLogic("QF_BV"); // quantifier free bitvector logic
	Type bitvector32 = em.mkBitVectorType(32);
	auto min = std::numeric_limits<T>::min();
	auto max = std::numeric_limits<T>::max();
	auto proc = [] (T val, ExprManager &em, SmtEngine &smt, auto conv) -> void {
		unsigned int width = 8 * sizeof(T);
		Expr bv = em.mkConst(BitVector(width, Integer(val)));
		//cout << bv << endl;
		auto ulc = bv.getConst<BitVector>().toInteger().getUnsignedLong();
		//cout << val << " = " << conv(ulc) << endl;
		auto res = conv(ulc);
		ASSERT_EQ(val, res);
		ASSERT_EQ(sizeof(T), sizeof(res));
		ASSERT_EQ(typeid(T), typeid(res));
	};

	auto conv = [] (unsigned long ulval) -> T {
		return ulval bitand (compl T(0));
	};

	std::list<T> val_list = {
			min,
			max,
			0,
			42
	};

	if (std::numeric_limits<T>::is_signed)
		val_list.push_back(-42);

	for (auto i = val_list.begin(); i != val_list.end(); i++) {
		proc(T(*i), em, smt, conv);
	}
}

TEST_F(CVC4EngineTest, Ability) {
	ability_test<std::int8_t>();
	ability_test<std::int16_t>();
	ability_test<std::int32_t>();
	ability_test<std::int64_t>();
	ability_test<std::uint8_t>();
	ability_test<std::uint16_t>();
	ability_test<std::uint32_t>();
	ability_test<std::uint64_t>();
}

TEST_F(CVC4EngineTest, Prism_nullptr) {
	bool nlp_ex = false;
	try {
		SharedExpr nlp = nullptr;
		Engine()->Prism(nlp);
	}
	catch (std::logic_error &e) {
		nlp_ex = true;
	}
	ASSERT_TRUE(nlp_ex);
}

TEST_F(CVC4EngineTest, Prism_Var) {
	// (declare-const NAME (_ BitVec 32))
	SharedExpr x = V("x");
	CVC4::Expr x_expr = Engine()->Prism(x);
	ASSERT_EQ("x", x_expr.toString());
}

//refactoring: tempalting
TEST_F(CVC4EngineTest, Prism_Const) {
	// (display (_ bv32 VAL))
	auto f = [] (std::int32_t val, CVC4Engine *engine) {
		auto x = C(val);
		engine->Push();
		CVC4::Expr expr = engine->Prism(x);
		CVC4::BitVector btv_const = expr.getConst<CVC4::BitVector>();
		auto int_val = engine->FromBitVector(btv_const);
		ASSERT_EQ(val, int_val);
		engine->Pop();
	};

	std::list<std::int32_t> val_list = {
			0,
			42,
			214,
			-42,
			INT32_MAX,
			INT32_MIN
	};

	for (std::list<std::int32_t>::iterator i = val_list.begin(); i != val_list.end(); i++) {
		f(*i, Engine());
	}
}

TEST_F(CVC4EngineTest, GetValue) {
	// (declare-const x (_ BitVec 32))
	// (assert (= x VAL))
	// (check-sat)
	// (get-value (x))
	//TODO:
}
}













