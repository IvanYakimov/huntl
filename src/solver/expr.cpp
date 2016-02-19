# include "expr.hpp"

using std::function;

namespace solver
{//-------------------------------------------------------------------
	//-------------------------------------------------------------------
	// Variable
	//TODO: solver compilation problem

	Var::Var (std::string name, TypePtr type) throw(std::logic_error) {
		if (not name.empty() and type != nullptr) {
			name_ = name;
			type_ = type;
		}
		else
			throw std::logic_error("invalid arguments");
	}

	Var::~Var() {}

	bool Var::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.name_ == rhs.name_
					and lhs.type_ == rhs.type_;
		};
		return EqualsHelper<Var>(*this, rhs, cmp);
	}

	std::string Var::ToString() const {return GetName();}
	std::string Var::GetName() const {return name_;}
	TypePtr Var::GetType() const {return type_;}

	//-------------------------------------------------------------------
	// Constant

	Const::Const(ValuePtr val) throw(std::logic_error) {
		if (val != nullptr)
			value_ = val;
		else
			throw std::logic_error("null not available");
	}

	Const::~Const() {}

	bool Const::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.GetValue() == rhs.GetValue();
		};
		return EqualsHelper<Const>(*this, rhs, cmp);
	}

	std::string Const::ToString() const {
		return GetValue()->ToString();
	}

	ValuePtr Const::GetValue() const {
		return value_;
	}

	//-------------------------------------------------------------------
	// BinaryOperation
	BinOp::BinOp(ExprPtr l, ExprPtr r, Kind k){
		if (l == nullptr or r == nullptr)
			throw std::logic_error("null not valid");
		kind_ = k;
		left_child_ = l;
		right_child_ = r;
	}

	BinOp::~BinOp() {}

	bool BinOp::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.kind_ == rhs.kind_ &&
					lhs.left_child_ == rhs.left_child_ &&
					lhs.right_child_ == rhs.right_child_;
		};
		return EqualsHelper<BinOp>(*this, rhs, cmp);
	}

	std::string BinOp::ToString() const {
		return GetKindName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}

	ExprPtr BinOp::GetLeftChild() const {return left_child_;}
	ExprPtr BinOp::GetRightChild() const {return right_child_;}

	Kind BinOp::GetKind() const {return kind_;}
	std::string BinOp::GetKindName() const {return KindToString(kind_);}

}













