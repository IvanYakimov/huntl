# include "expr.hpp"

using std::function;

namespace solver
{
//-------------------------------------------------------------------
// Factory
SharedExprPtr ExprFactory :: ProduceVariable (std::string name) {
	return std::make_shared <Variable>(name);
}

SharedExprPtr ExprFactory :: ProduceConstantI32 (std::int32_t val) {
	return std::make_shared <ConstantI32>(val);
}

SharedExprPtr ExprFactory :: ProduceBinaryOperation (SharedExprPtr a, SharedExprPtr b, Kind op_code) {
return std::make_shared <BinaryOperation>(a, b, op_code);
}

//-------------------------------------------------------------------
// Expr

//TODO: refactoring - extract pattern code

SharedExprPtr slt(SharedExprPtr l, SharedExprPtr r){
	return ExprFactory::ProduceBinaryOperation(l, r, Kind::SIGNED_LESS_THAN);
}

SharedExprPtr slt(SharedExprPtr l, std::int32_t r) {
	auto other = ExprFactory::ProduceConstantI32(r);
	return slt(l, other);
}

SharedExprPtr slt(std::int32_t l, SharedExprPtr r) {
	auto other = ExprFactory::ProduceConstantI32(l);
	return slt(other, r);
}

SharedExprPtr eq(SharedExprPtr l, SharedExprPtr r) {
	return ExprFactory::ProduceBinaryOperation(l, r, Kind::EQUAL);
}

SharedExprPtr eq(SharedExprPtr l, std::int32_t r) {
	auto other = ExprFactory::ProduceConstantI32(r);
	return eq(l, other);
}

SharedExprPtr eq(std::int32_t l, SharedExprPtr r) {
	auto other = ExprFactory::ProduceConstantI32(l);
	return eq(other, r);
}

//-------------------------------------------------------------------
// Variable
Variable::Variable (std::string name) {name_ = name;}
Variable::~Variable() {}

const std::string Variable::ToString() {return GetName();}

bool Variable::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.name_ == rhs.name_;
	};
	return EqualsHelper<Variable>(*this, rhs, cmp);
}

const std::string Variable::GetName() const {return name_;}

//-------------------------------------------------------------------
// Constant

ConstantI32::ConstantI32(std::int32_t value) : value_(value) {}
ConstantI32::~ConstantI32() {}

const std::string ConstantI32::ToString() {
	return std::to_string(GetValue());
}

bool ConstantI32::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.GetValue() == rhs.GetValue();
	};
	return EqualsHelper<ConstantI32>(*this, rhs, cmp);
}

std::int32_t ConstantI32::GetValue() {
	return value_;
}

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













