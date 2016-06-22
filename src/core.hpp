#ifndef __CORE_HPP__
#define __CORE_HPP__

#include "expr.hpp"

namespace solver {
	class Bool : public Expr {
	};

	using BoolPtr = std::shared_ptr<Bool>;

	enum class EqualityKind {
		EQUAL
	};

	class Equality : public DoubleNode<Bool, EqualityKind,
		ExprPtr, ExprPtr, BoolPtr> {};

	enum class DistinctKind {
		DISTINCT
	};

	class Distinct : public DoubleNode<Bool, DistinctKind,
		ExprPtr, ExprPtr, BoolPtr> {};

	enum class IfThenElseKind {
		IF_THEN_ELSE
	};

	class IfThenElse : public TripleNode<Bool, IfThenElseKind,
		ExprPtr, ExprPtr, ExprPtr, BoolPtr> {};

	class Value {
	private:
		bool value_;
	};
}

#endif












