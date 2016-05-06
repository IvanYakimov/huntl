#include "object-stub.hpp"

IndexCache<int> ObjectStub::id_cache_(1);

ObjectStub::ObjectStub() {
	id_ = id_cache_.Get();
}

ObjectStub::~ObjectStub() {
	id_cache_.PushBack(id_);
}

bool ObjectStub::Equals (const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) {
		return lhs.id_ == rhs.id_;
	};
	return EqualsHelper<ObjectStub>(*this, rhs, cmp);
}

std::string ObjectStub::ToString() const {
	return "object #" + std::to_string(id_);
}

ObjectStubPtr ObjectStub::Stub(ObjectPtr ptr) {
	return std::dynamic_pointer_cast<ObjectStub>(ptr);
}













