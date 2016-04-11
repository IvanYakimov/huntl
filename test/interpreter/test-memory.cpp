// Google Test
#include "gtest/gtest.h"
#include "../../src/interpreter/memory.hpp"
#include "../../src/utils/object.hpp"
#include "../../src/utils/index-cache.hpp"

#include <exception>
#include <iostream>
#include <memory>

//TODO: test contracts themselves!
//TODO: test object stub itselfy
namespace interpreter {
	using std::cout;
	using std::endl;
	using std::make_shared;

	class ObjectStub;
	using ObjectStubPtr = std::shared_ptr<ObjectStub>;

	class ObjectStub final : public CRTP<ObjectStub, Immutable> {
	public:
		ObjectStub() {
			id_ = id_cache_.Get();
		}

		~ObjectStub() {
			id_cache_.PushBack(id_);
		}

		virtual bool Equals (const Object& rhs) const {
			auto cmp = [] (auto lhs, auto rhs) {
				return lhs.id_ == rhs.id_;
			};
			return EqualsHelper<ObjectStub>(*this, rhs, cmp);
		}

		virtual std::string ToString() const {
			return "object #" + std::to_string(id_);
		}

	private:
		static IndexCache<int> id_cache_;
		int id_;
	};


	IndexCache<int> ObjectStub::id_cache_(0);

	ObjectStubPtr MkObj() {
		return std::make_shared<ObjectStub>();
	}

	ObjectStubPtr Stub(ObjectPtr obj_ptr) {
		return std::dynamic_pointer_cast<ObjectStub>(obj_ptr);
	}

	class MemoryTest : public ::testing::Test {
	public:
		MemoryTest () : id_cache_(1) {}
		StateId MkSt() {
				return id_cache_.Get();
		}
	private:
		IndexCache<StateId> id_cache_;
	};

	TEST_F(MemoryTest, contract__enabled) {
#ifndef CONTRACT
		FAIL() << "contract programming option not enabled";
#elif ! defined PRE
		FAIL() << "preconditions undefined";
#elif ! defined POST
		FAIL() << "postconditions undefined";
#endif
	}

	TEST_F(MemoryTest, Creation_Destruction) {
		Memory m;
	}

	TEST_F(MemoryTest, Allocate__basic) {
		try {
			auto obj_1 = MkObj();
			auto obj_2 = MkObj();
			StateId s1 = MkSt();
			StateId s2 = MkSt();
			Memory m;

			auto addr_1 = m.Allocate(s1, obj_1);
			auto addr_2 = m.Allocate(s2, obj_2);

			m.Free(addr_1, s1);
			m.Free(addr_2, s2);

			ASSERT_NE(addr_1, addr_2);
			ASSERT_NE(obj_1, obj_2);
			ASSERT_NE(*obj_1, *obj_2);
		} catch (std::exception& ex) {
			FAIL();
		}
	}

	TEST_F(MemoryTest, Share__basic) {
		try {
			auto obj_1 = MkObj();
			StateId s1 = MkSt();
			StateId s2 = MkSt();
			Memory m;

			auto addr_1 = m.Allocate(s1, obj_1);
			m.Share(addr_1, s1, s2);

			auto obj_1_1 = m.Read(addr_1, s1);
			auto obj_1_2 = m.Read(addr_1, s2);

			ASSERT_EQ(obj_1_1, obj_1_2);
			ASSERT_EQ(*Stub(obj_1_1), *Stub(obj_1_2));

			m.Free(addr_1, s1);
			m.Free(addr_1, s2);
		} catch (std::exception &ex) {
			FAIL();
		}
	}

	TEST_F(MemoryTest, Write__basic) {
		try {
			auto ob1 = MkObj();
			auto ob2 = MkObj();
			auto st1 = MkSt();
			auto st2 = MkSt();

			Memory m;

			auto ad1 = m.Allocate(st1, ob1);
			m.Share(ad1, st1, st2);
			auto ad2 = m.Write(ad1, st2, ob2);

			ASSERT_NE(ad1, ad2);

			m.Free(ad1, st1);
			m.Free(ad2, st2);
		} catch (std::exception &ex) {
			FAIL();
		}
	}

	TEST_F(MemoryTest, Write__basic_2) {
		try {
			auto ob1 = MkObj();
			auto st1 = MkSt();

			Memory m;
			auto ad1 = m.Allocate(st1);
			auto ad2 = m.Write(ad1, st1, ob1);

			ASSERT_EQ(ad1, ad2);

			auto ob2 = m.Read(ad1, st1);

			ASSERT_EQ(*Stub(ob1), *Stub(ob2));

			m.Free(ad1, st1);
		}
		catch (std::exception &ex) {
			FAIL();
		}
	}
}


















