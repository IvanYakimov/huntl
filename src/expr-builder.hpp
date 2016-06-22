#ifndef __EXPR_BUILDER_HPP__
#define __EXPR_BUILDER_HPP__

#include <cvc4/cvc4.h>

#include "context.hpp"

namespace solver {
	using ExprPtr = const CVC4::Expr&;
	using Kind = CVC4::Kind;

	class ExprBuilder {
	public:
		ExprBuilder(ContextRef context);
		ExprPtr MkExpr(Kind kind, ExprPtr child1);
		ExprPtr MkExpr(Kind kind, ExprPtr child1, ExprPtr child2);
	private:
		ContextRef context_;
		CVC4::ExprManager em;
	};
}

#endif
