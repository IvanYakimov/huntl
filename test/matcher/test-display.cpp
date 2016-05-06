#include "test-display.hpp"

using namespace interpreter;

class DisplayTest : public ::testing::Test {
public:
};

TEST_F (DisplayTest, basic) {
	DisplayPtr display = Display::Create();
	ObjectPtr ob1 = ObjectStub::Create();
	ObjectPtr ob2 = ObjectStub::Create();
	std::function<ObjectStubPtr (ObjectPtr)> s = ObjectStub::Stub;
	VoidFunc f; {
		auto x = f.Alloca32("x");
		auto y = f.Alloca32("y");
		display->Push(x, ob1);
		display->Push(y, ob2);
		auto r1 = display->LookUp(x);
		auto r2 = display->LookUp(y);
		ASSERT_EQ(ob1, r1);
		ASSERT_EQ(*s(ob1), *s(r1));
		ASSERT_EQ(ob2, r2);
	}
}
