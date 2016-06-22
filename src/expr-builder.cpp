#include "expr-builder.hpp"

namespace solver {
	ExprBuilder::ExprBuilder(ContextRef context) : context_(context) {

	}

	ExprPtr ExprBuilder::MkExpr(Kind kind, ExprPtr child1) {
		return em.mkExpr(kind, child1);
	}

	ExprPtr ExprBuilder::MkExpr(Kind kind, ExprPtr child1, ExprPtr child2) {

	}
}
