#include "test-display.hpp"

using namespace interpreter;

class DisplayTest : public ::testing::Test {
public:
	std::function<ObjectStubPtr (ObjectPtr)> s = ObjectStub::Stub;
};

TEST_F (DisplayTest, basic) {
	DisplayPtr display = Display::Create();
	ObjectStub::Reset();
	ObjectPtr ob1 = ObjectStub::Create();
	ObjectPtr ob2 = ObjectStub::Create();
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

TEST_F (DisplayTest, stack) {
	DisplayPtr display = Display::Create();
	ObjectStub::Reset();
	ObjectPtr obj1 = ObjectStub::Create();
	ObjectPtr obj2 = ObjectStub::Create();
	ObjectPtr obj3 = ObjectStub::Create();
	std::cout << obj1->ToString() + obj2->ToString() + obj3->ToString();
	VoidFunc f; {
		auto x = f.Alloca32("x");
		//auto r1 = display->LookUp(x); // implement in separated file, write bash-script for assertion handling
		//ASSERT_EQ(r1, nullptr);
		display->Push(x, obj1);
		auto r = display->LookUp(x);
		ASSERT_EQ(obj1, r); ASSERT_EQ(*s(obj1), *s(r));
		display->Push(x, obj2);
		r = display->LookUp(x);
		ASSERT_EQ(obj2, r); ASSERT_EQ(*s(obj2), *s(r));
		display->Push(x, obj3);
		r = display->LookUp(x);
		ASSERT_EQ(obj3, r); ASSERT_EQ(*s(obj3), *s(r));
	}
	ASSERT_EQ(0, ObjectStub::check_sum);
}

TEST_F (DisplayTest, blump) {
	DisplayPtr display = Display::Create();
	ObjectStub::Reset();
	ObjectPtr obj1 = ObjectStub::Create();
	ObjectPtr obj2 = ObjectStub::Create();
	ObjectPtr obj3 = ObjectStub::Create();
}














