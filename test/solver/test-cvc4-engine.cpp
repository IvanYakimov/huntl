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
	SharedExprPtr mkvar(std::string name) {ExprFactory::ProduceVariable(name);}
	void SetUp() {engine_ = new CVC4Engine();}
	void TearDown() {delete engine_;}
	ISMTEngine *Engine() const { return engine_; }
private:
	ISMTEngine *engine_ = nullptr;
};

#ifdef NODEF
TEST_F(CVC4EngineTest, Scopes) {
	auto x = mkvar("x");
	auto e1 = eq(x, 1);
	Engine()->Assert(e1);
	Engine()->Push();
	{

	}
	Engine()->Pop();
	auto s = Engine()->CheckSat();
	ASSERT_EQ(s, SAT);
	auto x_val = Engine()->GetValue(x);
	ASSERT_EQ(x_val, 1);
}

TEST_F(CVC4EngineTest, INT_LT) {
	auto x = mkvar("x"),
			y = mkvar("y");
	auto e = lt(x, y);
	Engine()->Assert(e);
	auto status = Engine()->CheckSat();
	ASSERT_EQ(status, SAT);
	auto x_val = Engine()->GetValue(x);
	auto y_val = Engine()->GetValue(y);
	ASSERT_TRUE(x_val < y_val);
}

TEST_F(CVC4EngineTest, INT_EQ) {
	auto x = mkvar("x");
	auto y = mkvar("y");
	auto e = eq(x, 100);
	auto w = eq(y, -100);
	Engine()->Assert(e);
	Engine()->Assert(w);
	auto status = Engine()->CheckSat();
	ASSERT_EQ(status, SAT);
	auto x_val = Engine()->GetValue(x);
	ASSERT_TRUE(x_val == 100);
	auto y_val = Engine()->GetValue(y);
	ASSERT_TRUE(y_val == -100);
}
#endif
}





