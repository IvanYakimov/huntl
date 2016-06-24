#include "test-display.hpp"

using namespace memory;
using namespace utils;

class DisplayTest : public ::testing::Test {
public:
};

TEST_F (DisplayTest, basic) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);

		Display d;
		d.Alloca(x);
		auto l_undef = d.Load(x);
		ASSERT_TRUE(instanceof<Undef>(l_undef));
		d.Store(x, ObjHolder<int32_t>::Create(42));
		auto l_42 = d.Load(x);
		ASSERT_TRUE(instanceof<ObjHolder<int32_t>>(l_42));
	}
}













