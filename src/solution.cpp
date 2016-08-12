#include "solution.hpp"

namespace interpreter {
	Integer::Integer(MetaIntRef value) : value_(value){}
	SolutionPtr Integer::Create(MetaIntRef value) {
		return utils::Create<Integer>(value);
	}
	const MetaIntRef Integer::Get() const {
		return value_;
	}

	Array::Array() {}
	void Array::PushBack(MetaIntRef value) {
		val_list_.push_back(value);
	}
	MetaIntRef Array::GetElement(unsigned index) {
		assert (index <= val_list_.size());
		return val_list_[index];
	}
	SolutionPtr Array::Create() {
		return utils::Create<Array>();
	}

	Pointer::Pointer(SolutionPtr target) : target_(target) {}
	SolutionPtr Pointer::Dereference() {return target_;}
	SolutionPtr Pointer::Create(SolutionPtr target) {
		return utils::Create<Pointer>(target);
	}
}














