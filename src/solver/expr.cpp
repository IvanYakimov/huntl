# include "expr.hpp"

//TODO: documentation
//TODO: testing
using std::string;

namespace solver
{

string Variable::ToString() {
	return GetName();
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
