#include "object-stub.hpp"

IndexCache<int> ObjectStub::id_cache_(1);

ObjectStub::ObjectStub() {
	id_ = id_cache_.Get();
	std::cerr << "<- " << id_ << " id-cache: " << id_cache_.ToString() << " on " << this << "\n";
	check_sum++;
}

ObjectStub::~ObjectStub() {
	check_sum--;
}

bool ObjectStub::Equals (const Object& rhs) const {
	auto cmp = [&] (const ObjectStub& lhs, const ObjectStub& rhs) -> bool {
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

void ObjectStub::Reset() {
	id_cache_.Reset();
}


int ObjectStub::check_sum = 0;








