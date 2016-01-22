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

TEST_F(CVC4EngineTest, INT_LT) {
	auto x = mkvar("x"),
			y = mkvar("y");
	auto lt = x < y;
	Engine()->Assert(lt);
	auto status = Engine()->CheckSat();
	ASSERT_EQ(status, SAT);
	auto x_val = Engine()->GetValue(x);
	auto y_val = Engine()->GetValue(y);
	ASSERT_TRUE(x < y);
}

}





