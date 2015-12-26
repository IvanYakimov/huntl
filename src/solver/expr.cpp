# include "expr.hpp"

//TODO: documentation
//TODO: testing
using std::string;

namespace solver
{
	string Variable::ToString() {
		return GetName();
	}

	bool operator==(const Variable &lhs, const Variable &rhs) {
		return lhs.name_ == rhs.name_;
	}

	bool operator!=(const Variable &lhs, const Variable &rhs) {
		return !(lhs == rhs);
	}

	template <size_t W>
	string Constant<W>::ToString() {
		auto int_val = value_->to_ulong();
		return std::to_string(int_val);
	}

	string BinaryOperation::ToString() {
		//TODO: use foldr instead of "whitespacing" (?)
		return GetOpCodeName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}
}
