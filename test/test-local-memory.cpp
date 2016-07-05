#include "test-local-memory.hpp"

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

		LocalMemory d;
		auto holder = Concrete::Create(interpreter::MetaInt(32, 42));
		d.Alloca(x, holder);
		auto c = d.Load(x);
		ASSERT_TRUE(instanceof<Concrete>(c));
	}
}













