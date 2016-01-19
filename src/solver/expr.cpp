# include "expr.hpp"

using std::function;

namespace solver
{
	const std::string Variable::ToString() {
		return GetName();
	}

	bool Variable::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.name_ == rhs.name_;
		};
		return EqualsHelper<Variable>(*this, rhs, cmp);
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
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.value_ == rhs.value_;
		};
		return EqualsHelper<Constant<T>>(*this, rhs, cmp);
	}

	const std::string BinaryOperation::ToString() {
		return GetOpCodeName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}

	bool BinaryOperation::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.op_code_ == rhs.op_code_ &&
					lhs.left_child_ == rhs.left_child_ &&
					lhs.right_child_ == rhs.right_child_;
		};
		return EqualsHelper<BinaryOperation>(*this, rhs, cmp);
	}
}













