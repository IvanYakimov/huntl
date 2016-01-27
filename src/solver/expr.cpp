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
SharedExprPtr C(std::int32_t val) {
	return ExprFactory::MkConstI32(val);
}

SharedExprPtr V(std::string name) {
	return ExprFactory::MkVar(name);
}

SharedExprPtr Apply(SharedExprPtr l, SharedExprPtr r, Kind k) {
	return ExprFactory::MkBinOp(l, r, k);
}

SharedExprPtr Add(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::ADD); }
SharedExprPtr Sub(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SUB); }
SharedExprPtr Mul(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::MUL); }
SharedExprPtr Sdiv(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SDIV); }
SharedExprPtr Srem(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SREM); }
SharedExprPtr Udiv(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::UDIV); }
SharedExprPtr Urem(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::UREM); }
SharedExprPtr Shl(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SHL); }
SharedExprPtr Ashr(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::ASHR); }
SharedExprPtr Lshr(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::LSHR); }
SharedExprPtr And(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::AND); }
SharedExprPtr Or(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::OR); }
SharedExprPtr Xor(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::XOR); }
SharedExprPtr Eq(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::EQ); }
SharedExprPtr Ne(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::NE); }
SharedExprPtr Sge(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SGE); }
SharedExprPtr Sgt(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SGT); }
SharedExprPtr Sle(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SLE); }
SharedExprPtr Slt(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::SLT); }
SharedExprPtr Uge(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::UGE); }
SharedExprPtr Ugt(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::UGT); }
SharedExprPtr Ule(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::ULE); }
SharedExprPtr Ult(SharedExprPtr l, SharedExprPtr r) { return Apply(l, r, Kind::ULT); }

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













