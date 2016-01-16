# include "expr.hpp"

//TODO: documentation
//TODO: testing

namespace solver
{
	const std::string Variable::ToString() {
		return GetName();
	}

	bool Variable::Equals(const Object& rhs) const {
		return &rhs != nullptr && name_ == dynamic_cast<const Variable*>(&rhs)->name_;
	}

	template <size_t W>
	const std::string Constant<W>::ToString() {
		auto int_val = value_->to_ulong();
		return std::to_string(int_val);
	}

	template <size_t W>
	bool Constant<W>::Equals(const Object& rhs) const {
		return &rhs != nullptr && *value_ == *dynamic_cast<const Constant<W>*>(&rhs)->value_;
	}

	const std::string BinaryOperation::ToString() {
		//TODO: use foldr instead of "whitespacing" (?)
		return GetOpCodeName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}

	bool BinaryOperation::Equals(const Object& rhs) const {
		auto other = dynamic_cast<const BinaryOperation*> (&rhs);
		return &rhs != nullptr &&
				op_code_ == other->op_code_ &&
				left_child_ == other->left_child_ &&
				right_child_ == other->right_child_;
	}
}













