#ifndef __EXPR_HPP__
#define __EXPR_HPP__

#include <cvc4/cvc4.h>

namespace solver {
	using SharedExpr = CVC4::Expr;
	using BitVec = CVC4::BitVector;
	using InfiniteInt = CVC4::Integer;
}

#endif
