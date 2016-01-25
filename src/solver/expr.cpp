# include "expr.hpp"

using std::function;

namespace solver
{
//-------------------------------------------------------------------
// Factory
SharedExprPtr ExprFactory :: MkVar (std::string name) {
	return std::make_shared <Var>(name);
}

SharedExprPtr ExprFactory :: MkConstI32 (std::int32_t val) {
	return std::make_shared <ConstI32>(val);
}

SharedExprPtr ExprFactory :: MkBinOp (SharedExprPtr a, SharedExprPtr b, Kind op_code) {
return std::make_shared <BinOp>(a, b, op_code);
}

//-------------------------------------------------------------------
// Expr

//TODO: refactoring
SharedExprPtr slt(SharedExprPtr l, SharedExprPtr r){
	return ExprFactory::MkBinOp(l, r, Kind::SIGNED_LESS_THAN);
}

SharedExprPtr slt(SharedExprPtr l, std::int32_t r) {
	auto other = ExprFactory::MkConstI32(r);
	return slt(l, other);
}

SharedExprPtr slt(std::int32_t l, SharedExprPtr r) {
	auto other = ExprFactory::MkConstI32(l);
	return slt(other, r);
}

SharedExprPtr eq(SharedExprPtr l, SharedExprPtr r) {
	return ExprFactory::MkBinOp(l, r, Kind::EQUAL);
}

SharedExprPtr eq(SharedExprPtr l, std::int32_t r) {
	auto other = ExprFactory::MkConstI32(r);
	return eq(l, other);
}

SharedExprPtr eq(std::int32_t l, SharedExprPtr r) {
	auto other = ExprFactory::MkConstI32(l);
	return eq(other, r);
}

//-------------------------------------------------------------------
// Variable
Var::Var (std::string name) {name_ = name;}
Var::~Var() {}

const std::string Var::ToString() {return GetName();}

bool Var::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.name_ == rhs.name_;
	};
	return EqualsHelper<Var>(*this, rhs, cmp);
}

const std::string Var::GetName() const {return name_;}

//-------------------------------------------------------------------
// Constant

ConstI32::ConstI32(std::int32_t value) : value_(value) {}
ConstI32::~ConstI32() {}

const std::string ConstI32::ToString() {
	return std::to_string(GetValue());
}

bool ConstI32::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.GetValue() == rhs.GetValue();
	};
	return EqualsHelper<ConstI32>(*this, rhs, cmp);
}

std::int32_t ConstI32::GetValue() {
	return value_;
}

//-------------------------------------------------------------------
// BinaryOperation
BinOp::BinOp(SharedExprPtr left_child, SharedExprPtr right_child, Kind kind){
	    	kind_ = kind;
	    	left_child_ = left_child;
	    	right_child_ = right_child;
}

BinOp::~BinOp() {}

const std::string BinOp::ToString(){
	return GetKindName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
}

bool BinOp::Equals(const Object& rhs) const {
	auto cmp = [] (auto lhs, auto rhs) -> bool {
		return lhs.kind_ == rhs.kind_ &&
				lhs.left_child_ == rhs.left_child_ &&
				lhs.right_child_ == rhs.right_child_;
	};
	return EqualsHelper<BinOp>(*this, rhs, cmp);
}

SharedExprPtr BinOp::GetLeftChild() {return left_child_;}
SharedExprPtr BinOp::GetRightChild() {return right_child_;}

Kind BinOp::GetKind() {return kind_;}
std::string BinOp::GetKindName() {return KindToString(kind_);}

}













