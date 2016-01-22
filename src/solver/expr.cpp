# include "expr.hpp"

using std::function;

namespace solver
{
//-------------------------------------------------------------------
// Variable
Variable::Variable (std::string name) {name_ = name;}
Variable::~Variable() {}

const std::string Variable::ToString() {return GetName();}

SharedExprPtr Variable::Create(std::string name) {return std::make_shared<Variable>(name);}

bool Variable::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.name_ == rhs.name_;
	};
	return EqualsHelper<Variable>(*this, rhs, cmp);
}

const std::string Variable::GetName() const {return name_;}

//-------------------------------------------------------------------
// Constant
template <typename T>
Constant<T>::Constant(T value) {value_ = value;}
template <typename T>
Constant<T>::~Constant() {}

template <typename T>
const std::string Constant<T>::ToString() {return std::to_string(value_);}

template <typename T>
SharedExprPtr Constant<T>::Create(T value) {return std::make_shared<Constant<T>>(value);}

template <typename T>
bool Constant<T>::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.value_ == rhs.value_;
	};
	return EqualsHelper<Constant<T>>(*this, rhs, cmp);
}

template <typename T>
T Constant<T>::GetValue() {return value_;}

//-------------------------------------------------------------------
// BinaryOperation
BinaryOperation::BinaryOperation(SharedExprPtr left_child, SharedExprPtr right_child, Kind kind){
	    	kind_ = kind;
	    	left_child_ = left_child;
	    	right_child_ = right_child;
}

BinaryOperation::~BinaryOperation() {}

const std::string BinaryOperation::ToString(){
	return GetOpCodeName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
}

SharedExprPtr BinaryOperation::Create(SharedExprPtr left_child, SharedExprPtr right_child, Kind op_code) {
	return std::make_shared<BinaryOperation>(left_child, right_child, op_code);
}

bool BinaryOperation::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.kind_ == rhs.kind_ &&
				lhs.left_child_ == rhs.left_child_ &&
				lhs.right_child_ == rhs.right_child_;
	};
	return EqualsHelper<BinaryOperation>(*this, rhs, cmp);
}

SharedExprPtr BinaryOperation::GetLeftChild() {return left_child_;}
SharedExprPtr BinaryOperation::GetRightChild() {return right_child_;}

Kind BinaryOperation::GetOpCode() {return kind_;}
std::string BinaryOperation::GetOpCodeName() {return KindToString(kind_);}

}













