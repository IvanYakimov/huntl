// Project
# include "../../src/solver/expr.hpp"
# include "../../src/solver/expr-factory.hpp"
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
	void SetUp() {
		factory_ = new ExprFactory();
		engine_ = new CVC4Engine();
	}
	void TearDown() {
		delete factory_;
		delete engine_;
	}
	ExprFactory *Factory() const { return factory_ ; }
	ISMTEngine *Engine() const { return engine_; }
private:
	ExprFactory *factory_ = nullptr;
	ISMTEngine *engine_ = nullptr;
};

TEST_F(CVC4EngineTest, INT_LT) {
	auto x = Factory()->ProduceVariable("x"),
			y = Factory()->ProduceVariable("y");
	auto lt = Factory()->ProduceBinaryOperation(x, y, BinaryOperation::LESS_THAN);
	Engine()->Assert(lt);
	auto status = Engine()->CheckSat();
	ASSERT_EQ(status, SAT);
	auto x_val = Engine()->GetValue(x);
	auto y_val = Engine()->GetValue(y);
	ASSERT_TRUE(x < y);
}

}





