# include "expr.hpp"

using std::function;

namespace solver
{
//-------------------------------------------------------------------
// Factory
SharedExpr ExprFactory :: MkVar (std::string name) {
	return std::make_shared <Var>(name);
}

SharedExpr ExprFactory :: MkConstI32 (std::int32_t val) {
	return std::make_shared <ConstI32>(val);
}

SharedExpr ExprFactory :: MkBinOp (SharedExpr a, SharedExpr b, Kind op_code) {
return std::make_shared <BinOp>(a, b, op_code);
}

//-------------------------------------------------------------------
// Expr
SharedExpr C(std::int32_t val) {
	return ExprFactory::MkConstI32(val);
}

SharedExpr V(std::string name) {
	return ExprFactory::MkVar(name);
}

SharedExpr Apply(SharedExpr l, SharedExpr r, Kind k) {
	return ExprFactory::MkBinOp(l, r, k);
}

SharedExpr Add(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::ADD); }
SharedExpr Sub(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SUB); }
SharedExpr Mul(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::MUL); }
SharedExpr Sdiv(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SDIV); }
SharedExpr Srem(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SREM); }
SharedExpr Udiv(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::UDIV); }
SharedExpr Urem(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::UREM); }
SharedExpr Shl(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SHL); }
SharedExpr Ashr(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::ASHR); }
SharedExpr Lshr(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::LSHR); }
SharedExpr And(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::AND); }
SharedExpr Or(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::OR); }
SharedExpr Xor(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::XOR); }
SharedExpr Eq(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::EQ); }
SharedExpr Ne(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::NE); }
SharedExpr Sge(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SGE); }
SharedExpr Sgt(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SGT); }
SharedExpr Sle(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SLE); }
SharedExpr Slt(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::SLT); }
SharedExpr Uge(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::UGE); }
SharedExpr Ugt(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::UGT); }
SharedExpr Ule(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::ULE); }
SharedExpr Ult(SharedExpr l, SharedExpr r) { return Apply(l, r, Kind::ULT); }

//-------------------------------------------------------------------
// Variable
//TODO: solver compilation problem

Var::Var (std::string name) {
	if (not name.empty())
		name_ = name;
	else
		throw std::logic_error("empty string not valid");
}
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
BinOp::BinOp(SharedExpr l, SharedExpr r, Kind k){
	if (l == nullptr or r == nullptr)
		throw std::logic_error("null not valid");
	kind_ = k;
	left_child_ = l;
	right_child_ = r;
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

SharedExpr BinOp::GetLeftChild() {return left_child_;}
SharedExpr BinOp::GetRightChild() {return right_child_;}

Kind BinOp::GetKind() {return kind_;}
std::string BinOp::GetKindName() {return KindToString(kind_);}

}













