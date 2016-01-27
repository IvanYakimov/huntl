// Project
# include "../../src/solver/expr.hpp"
# include "../../src/solver/ismt-engine.hpp"
# include "../../src/solver/cvc4-engine.hpp"

// Google Test
# include "gtest/gtest.h"

//STL
#include <memory>
#include <iostream>

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
	std::int32_t val = 28;
	auto x = C(28);
	//CVC4::Expr expr = Engine()->Prism(x);
	//std::cout << x;
}
}













