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

	template <size_t W>
	const std::string Constant<W>::ToString() {
		auto int_val = value_->to_ulong();
		return std::to_string(int_val);
	}

	template <size_t W>
	long Constant<W>::GetValue() {
		signed long result = 0;
		unsigned long from = value_->to_ulong();
		std::memcpy(&result, &from, sizeof(signed long));
		return result;
	}

	template <size_t W>
	bool Constant<W>::Equals(const Object& rhs) const {
		auto other = dynamic_cast<const Constant<W>*>(&rhs);
		if (!other)
			return false;
		else
			return &rhs != nullptr && *value_ == *(other->value_);
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













