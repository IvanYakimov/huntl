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
	//-------------------------------------------------------------------------
	// Node hierachy
	Node::Node(Kind kind) : kind_(kind) {}

	Node::~Node() {}

	Kind Node::GetKind() const {
		return kind_;
	}

	std::string Node::GetKindName() const {
		return to_string(kind_);
	}

	DoubleNode::DoubleNode(ExprPtr l, ExprPtr r, Kind k) throw (IllegalArgException) : Node(k) {
		if (l == nullptr or r == nullptr)
			throw IllegalArgException();
		left_child_ = l;
		right_child_ = r;
	}

	DoubleNode::~DoubleNode() {}

	bool DoubleNode::Equals(const Object& rhs) const {
		auto cmp = [] (const DoubleNode &lhs, const DoubleNode &rhs) -> bool {
			return lhs.GetKind() == rhs.GetKind() &&
					lhs.left_child_ == rhs.left_child_ &&
					lhs.right_child_ == rhs.right_child_;
		};
		return EqualsHelper<DoubleNode>(*this, rhs, cmp);
	}

	std::string DoubleNode::ToString() const {
		return "(" + GetKindName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString() + ")";
	}

	ExprPtr DoubleNode::GetLeftChild() const {return left_child_;}
	ExprPtr DoubleNode::GetRightChild() const {return right_child_;}
}













