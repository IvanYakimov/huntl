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

template<std::size_t size, typename T>
void ability_test() {
	using namespace ::CVC4;
	using Expr = ::CVC4::Expr;
	using std::cout;
	using std::endl;
	ExprManager em;
	SmtEngine smt(&em);
	smt.setLogic("QF_BV"); // quantifier free bitvector logic
	Type bitvector32 = em.mkBitVectorType(32);
	Expr x = em.mkVar("x", bitvector32),
			y = em.mkVar("y", bitvector32);
	auto min = std::numeric_limits<std::int32_t>::min();
	auto max = std::numeric_limits<std::int32_t>::max();
	Expr c0 = em.mkConst(BitVector(32, Integer(0)));
	Expr c42 = em.mkConst(BitVector(32, Integer(42)));
	Expr cn42 = em.mkConst(BitVector(32, Integer(-42)));
	Expr cmax = em.mkConst(BitVector(32, Integer(max)));
	Expr cmin = em.mkConst(BitVector(32, Integer(min)));
	cout << c0 << endl;
	cout << c42 << endl;
	cout << cn42 << endl;
	cout << cmax << endl;
	cout << cmin << endl;
	auto c0_L = c0.getConst<BitVector>().toInteger().getUnsignedLong();
	auto c42_L = c42.getConst<BitVector>().toInteger().getUnsignedLong();
	auto cn42_L = cn42.getConst<BitVector>().toInteger().getUnsignedLong();
	auto cmax_L = cmax.getConst<BitVector>().toInteger().getUnsignedLong();
	auto cmin_L = cmin.getConst<BitVector>().toInteger().getUnsignedLong();
	auto conv = [] (unsigned long long_val) -> std::int32_t {
		return long_val bitand (compl 0);
	};
	cout << 0 << " = " << conv(c0_L) << endl;
	cout << 42 << " = " << conv(c42_L) << endl;
	cout << -42 << " = " << conv(cn42_L) << endl;
	cout << max << " = " << conv(cmax_L) << endl;
	cout << min << " = " << conv(cmin_L) << endl;
}

TEST_F(CVC4EngineTest, Ability) {
	using namespace ::CVC4;
	using Expr = ::CVC4::Expr;
	using std::cout;
	using std::endl;
	ExprManager em;
	SmtEngine smt(&em);
	smt.setLogic("QF_BV"); // quantifier free bitvector logic
	Type bitvector32 = em.mkBitVectorType(32);
	Expr x = em.mkVar("x", bitvector32),
			y = em.mkVar("y", bitvector32);
	auto min = std::numeric_limits<std::int32_t>::min();
	auto max = std::numeric_limits<std::int32_t>::max();
	Expr c0 = em.mkConst(BitVector(32, Integer(0)));
	Expr c42 = em.mkConst(BitVector(32, Integer(42)));
	Expr cn42 = em.mkConst(BitVector(32, Integer(-42)));
	Expr cmax = em.mkConst(BitVector(32, Integer(max)));
	Expr cmin = em.mkConst(BitVector(32, Integer(min)));
	cout << c0 << endl;
	cout << c42 << endl;
	cout << cn42 << endl;
	cout << cmax << endl;
	cout << cmin << endl;
	auto c0_L = c0.getConst<BitVector>().toInteger().getUnsignedLong();
	auto c42_L = c42.getConst<BitVector>().toInteger().getUnsignedLong();
	auto cn42_L = cn42.getConst<BitVector>().toInteger().getUnsignedLong();
	auto cmax_L = cmax.getConst<BitVector>().toInteger().getUnsignedLong();
	auto cmin_L = cmin.getConst<BitVector>().toInteger().getUnsignedLong();
	auto conv = [] (unsigned long long_val) -> std::int32_t {
		return long_val bitand (compl 0);
	};
	cout << 0 << " = " << conv(c0_L) << endl;
	cout << 42 << " = " << conv(c42_L) << endl;
	cout << -42 << " = " << conv(cn42_L) << endl;
	cout << max << " = " << conv(cmax_L) << endl;
	cout << min << " = " << conv(cmin_L) << endl;
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
	auto c = C(42);
	auto x = V("x");
	auto e = Eq(x, c);
	Engine()->Assert(e);
	Engine()->CheckSat();
	std::int32_t val = Engine()->GetValue(x);
	//ASSERT_EQ(42, val);
}
}













