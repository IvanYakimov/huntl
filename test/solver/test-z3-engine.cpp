// Google Test
# include "gtest/gtest.h"

// Z3
# include "z3++.h"

namespace solver {
	class Z3EngineTest : public ::testing::Test {
	public:
	};

	// read more about this here: http://stackoverflow.com/questions/24252947/import-z3-model-value-to-c
	// http://z3prover.github.io/api/html/group__capi.html#ga2d57bd6f0d1cb1f98835a5f38a9dc4bb

	TEST_F(Z3EngineTest, Ability) {
		using namespace ::z3;
		using namespace ::std;
		context c;
		expr x = c.bv_val(42, 32);
		int val;
		Z3_get_numeral_int(c, x, &val);
		cout << val << endl;
	}
}

















