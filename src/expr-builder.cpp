#include "expr-builder.hpp"

namespace solver {
	ExprBuilder::ExprBuilder(ContextRef context) : context_(context) {

	}

	ExprRef ExprBuilder::MkExpr(Kind kind, ExprRef child1) {
		return context_.ExprManger().mkExpr(kind, child1);
	}

	ExprRef ExprBuilder::MkExpr(Kind kind, ExprRef child1, ExprRef child2) {
		return context_.ExprManger(kind, child1, child2);
	}
}
