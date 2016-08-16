#ifndef __EXPR_HPP__
#define __EXPR_HPP__

#include <cvc4/cvc4.h>

namespace solver {
	using SharedExpr = CVC4::Expr;
	using Type = CVC4::Type;
	using BitVec = CVC4::BitVector;
	using BitVecTy = CVC4::BitVectorType;
	using InfiniteInt = CVC4::Integer;
}

#endif
