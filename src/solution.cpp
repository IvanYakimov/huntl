#include "solution.hpp"

namespace interpreter {
	Integer::Integer(HolderPtr value) : value_(value){
	}

	IntegerPtr Integer::Create(HolderPtr value) {
		return utils::Create<Integer>(value);
	}

	const HolderPtr Integer::Get() const {
		return value_;
	}

	bool Integer::IsChar() {
		if (interpreter::GetWidth(Get()) == 8) {
			return true; }
	}

	Array::Array() {
	}

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

	bool Array::IsString() {
		assert (GetSize() > 0);
		if (utils::instanceof<Integer>(GetElement(0))) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(GetElement(0));
			return integer->IsChar(); }
	}

	Pointer::Pointer(SolutionPtr target) : target_(target) {
	}

	SolutionPtr Pointer::Dereference() {return target_;
	}

	PointerPtr Pointer::Create(SolutionPtr target) {
		return utils::Create<Pointer>(target);
	}

	IntegerPtr ToInteger(SolutionPtr solution) {
		IntegerPtr res = std::dynamic_pointer_cast<Integer>(solution);
		assert (res != nullptr and "cast error");
		return res;
	}
}














