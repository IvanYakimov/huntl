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
	void Array::PushBack(SolutionPtr value) {
		val_list_.push_back(value);
	}
	SolutionPtr Array::GetElement(unsigned index) {
		assert (index <= val_list_.size());
		return val_list_[index];
	}
	ArrayPtr Array::Create() {
		return utils::Create<Array>();
	}
	unsigned Array::GetSize() {
		return val_list_.size();
	}

	Pointer::Pointer(SolutionPtr target) : target_(target) {}
	SolutionPtr Pointer::Dereference() {return target_;}
	SolutionPtr Pointer::Create(SolutionPtr target) {
		return utils::Create<Pointer>(target);
	}
}













