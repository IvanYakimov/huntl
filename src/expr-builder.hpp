#ifndef __EXPR_BUILDER_HPP__
#define __EXPR_BUILDER_HPP__

#include <cvc4/cvc4.h>

#include "context.hpp"

namespace solver {
	using ExprRef = const CVC4::Expr&;
	using Kind = CVC4::Kind;

	class ExprBuilder {
	public:
		ExprBuilder(ContextRef context);
		ExprRef MkExpr(Kind kind, ExprRef child1);
		ExprRef MkExpr(Kind kind, ExprRef child1, ExprRef child2);
		ExprRef MkExpr(Kind kind, ExprRef child1, ExprRef child2, ExprRef child3);
	private:
		ContextRef context_;
		CVC4::ExprManager em;
	};
}

#endif
