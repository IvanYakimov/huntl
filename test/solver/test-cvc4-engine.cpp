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
class CVC4EngineTest : public ::testing::Test {
public:
	SharedExprPtr mkvar(std::string name) {ExprFactory::MkVar(name);}
	void SetUp() {engine_ = new CVC4Engine();}
	void TearDown() {delete engine_;}
	CVC4Engine *Engine() const { return engine_; }
private:
	CVC4Engine *engine_ = nullptr;
};

TEST_F(CVC4EngineTest, Prism_Var) {
	auto name = "x";
	auto x = V(name);
	CVC4::Expr expr = Engine()->Prism(x);
	ASSERT_EQ(name, expr.toString());
}

TEST_F(CVC4EngineTest, Prism_Const) {
	auto f = [] (std::int32_t val, CVC4Engine *engine) {
		auto x = C(val);
		engine->Push();
		CVC4::Expr expr = engine->Prism(x);
		CVC4::BitVector btv_const = expr.getConst<CVC4::BitVector>();
		CVC4::Integer integer_const = btv_const.toInteger();
		std::int32_t int_const = integer_const.getSignedInt();
		std::cout << val << std::endl;
		std::cout << int_const << std::endl;
		ASSERT_EQ(val, int_const);
		engine->Pop();
	};

	std::list<std::int32_t> val_list = {
			0,
			28,
			-28,
			INT32_MIN,
			INT32_MAX
	};

	for (std::list<std::int32_t>::iterator i = val_list.begin(); i != val_list.end(); i++) {
		f(*i, Engine());
	}
}
}













