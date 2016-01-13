# include "expr.hpp"

//TODO: documentation
//TODO: testing

namespace solver
{
	const std::string Variable::ToString() {
		return GetName();
	}

	bool Variable::Equals(Variable const &rhs) const {
		return true;
	}

# ifdef UNDEF
	template <size_t W>
	string Constant<W>::ToString() {
		auto int_val = value_->to_ulong();
		return std::to_string(int_val);
	}

	string BinaryOperation::ToString() {
		//TODO: use foldr instead of "whitespacing" (?)
		return GetOpCodeName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}
# endif
}
