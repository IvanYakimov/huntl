# include "expr.hpp"

using std::function;

namespace solver
{
	Var::Var (std::string name, TypePtr type) throw(IllegalArgException) {
		if (not name.empty() and type != nullptr) {
			name_ = name;
			type_ = type;
			id_ = id_cache_.Get();
		}
		else
			throw IllegalArgException();
	}

	Var::~Var() {
	}

	IndexCache<uint64_t> Var::id_cache_(1);

	bool Var::Equals(const Object& rhs) const {
		auto cmp = [] (const Var &lhs, const Var &rhs) -> bool {
			return lhs.name_ == rhs.name_
					and lhs.type_ == rhs.type_
					and lhs.id_ == rhs.id_;
		};
		return EqualsHelper<Var>(*this, rhs, cmp);
	}

	std::string Var::ToString() const {
		return GetType()->ToString() + " " + GetName() + ":s" + std::to_string(id_);
	}
	std::string Var::GetName() const {return name_;}
	TypePtr Var::GetType() const {return type_;}
	void Var::Reset() { id_cache_.Reset(); }

	Const::Const(ValuePtr val) throw(IllegalArgException) {
		if (val != nullptr)
			value_ = val;
		else
			throw IllegalArgException();
	}

	Const::~Const() {}

	bool Const::Equals(const Object& rhs) const {
		auto cmp = [] (const Const &lhs, const Const &rhs) -> bool {
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

	BinOp::BinOp(ExprPtr l, ExprPtr r, Kind k) throw (IllegalArgException) {
		if (l == nullptr or r == nullptr)
			throw IllegalArgException();
		kind_ = k;
		left_child_ = l;
		right_child_ = r;
	}

	BinOp::~BinOp() {}

	bool BinOp::Equals(const Object& rhs) const {
		auto cmp = [] (const BinOp &lhs, const BinOp &rhs) -> bool {
			return lhs.kind_ == rhs.kind_ &&
					lhs.left_child_ == rhs.left_child_ &&
					lhs.right_child_ == rhs.right_child_;
		};
		return EqualsHelper<BinOp>(*this, rhs, cmp);
	}

	std::string BinOp::ToString() const {
		return "(" + GetKindName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString() + ")";
	}

	ExprPtr BinOp::GetLeftChild() const {return left_child_;}
	ExprPtr BinOp::GetRightChild() const {return right_child_;}

	Kind BinOp::GetKind() const {return kind_;}
	std::string BinOp::GetKindName() const {return to_string(kind_);}

}













