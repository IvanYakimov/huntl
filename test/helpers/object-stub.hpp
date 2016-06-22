#ifndef __OBJECT_STUB_HPP__
#define __OBJECT_STUB_HPP__

#include "../../src/utils/object.hpp"
#include "../../src/utils/index-cache.hpp"
#include "../../src/utils/creatable.hpp"

class ObjectStub;
using ObjectStubPtr = std::shared_ptr<ObjectStub>;
using utils::creatable;

class ObjectStub final : public creatable<ObjectStub, Immutable> {
public:
	ObjectStub();
	ObjectStub(const ObjectStub& rhs) = delete;
	~ObjectStub();
	virtual bool Equals (const Object& rhs) const;
	virtual std::string ToString() const;
	static ObjectStubPtr Stub(ObjectPtr ptr);
	static void Reset();
	static IndexCache<int> id_cache_;
	int id_;
	static int check_sum;
};



#endif















