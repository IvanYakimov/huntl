#ifndef __EXPR_MANAGER_HELPER_HPP__
#define __EXPR_MANAGER_HELPER_HPP__

#pragma once

#include "expr.hpp"
#include "object-builder.hpp"

#include <functional>

namespace solver {
	/** Helper function.
	 *  \attention Warning: do not use this helper functions in the main project
	 *  \note Use them in an appropriate test suites. */
	static ExprPtr Apply(ExprPtr left, ExprPtr right, Kind kind) {
		return ObjectBuilder::Get()->MkDoubleNode(left, right, kind);
	}

	using Func = std::function<ExprPtr(ExprPtr,ExprPtr)>;

	static ExprPtr Add(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::ADD); }
	static ExprPtr Sub(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SUB); }
	static ExprPtr Mul(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::MUL); }
	static ExprPtr SDiv (ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SDIV); }
	static ExprPtr SRem(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SREM); }
	static ExprPtr UDiv(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::UDIV); }
	static ExprPtr URem(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::UREM); }
	static ExprPtr And(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::AND); }
	static ExprPtr Shl(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SHL); }
	static ExprPtr LShr(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::LSHR); }
	static ExprPtr AShr(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::ASHR); }
	static ExprPtr Or(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::OR); }
	static ExprPtr Xor(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::XOR); }
	static ExprPtr Equal(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::EQUAL); }
	static ExprPtr Distinct(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::DISTINCT); }
	static ExprPtr UGt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::UGT); }
	static ExprPtr UGe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::UGE); }
	static ExprPtr ULt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::ULT); }
	static ExprPtr ULe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::ULE); }
	static ExprPtr SGt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SGT); }
	static ExprPtr SGe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SGE); }
	static ExprPtr SLt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SLT); }
	static ExprPtr SLe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SLE); }

	/** Helper function - returns new constant.
	 *  \attention Warning: do not use this helper functions in the main project
	 *  \note Use them in an appropriate test suites. */
	template<typename T> ExprPtr C(T val) { return ObjectBuilder::Get()->MkConst(ObjectBuilder::Get()->MkIntVal<T>(val)); }
	/** Helper function - returns new variable.
	 *  \attention Warning: do not use this helper functions in the main project
	 *  \note Use them in an appropriate test suites. */
	template<typename T> ExprPtr V(std::string name) { return ObjectBuilder::Get()->MkVar(name, ObjectBuilder::Get()->MkIntTy<T>()); }
}

#endif /* __EXPR_MANAGER_HELPER_HPP__ */













