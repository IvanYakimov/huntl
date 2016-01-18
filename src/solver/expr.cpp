# include "expr.hpp"

//TODO: documentation
//TODO: testing

namespace solver
{
	const std::string Variable::ToString() {
		return GetName();
	}

	bool Variable::Equals(const Object& rhs) const {
		auto other = dynamic_cast<const Variable*>(&rhs);
		if (!other)
			return false;
		else
			return &rhs != nullptr && name_ == other->name_;
	}

	template <typename T>
	const std::string Constant<T>::ToString() {
		return std::to_string(value_);
	}

	template <typename T>
	T Constant<T>::GetValue() {
		return value_;
	}

	template <typename T>
	bool Constant<T>::Equals(const Object& rhs) const {
		auto other = dynamic_cast<const Constant<T>*>(&rhs);
		if (!other)
			return false;
		else
			return &rhs != nullptr && value_ == other->value_;
	}

	const std::string BinaryOperation::ToString() {
		return GetOpCodeName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}

	bool BinaryOperation::Equals(const Object& rhs) const {
		auto other = dynamic_cast<const BinaryOperation*> (&rhs);
		if (!other)
			return false;
		else
			return &rhs != nullptr &&
				op_code_ == other->op_code_ &&
				left_child_ == other->left_child_ &&
				right_child_ == other->right_child_;
	}
}













