#ifndef __EXPR_MANAGER_HELPER_HPP__
#define __EXPR_MANAGER_HELPER_HPP__
#pragma once

//-----------------------------------------------------------------------------
// Warning: do not use this helper functions in the main project,
// Use them in an appropriate test suites.
//-----------------------------------------------------------------------------

#include "expr.hpp"
#include "expr-manager.hpp"

#include <functional>

namespace solver {
	namespace expr_manager_helper {
		static ExprPtr Apply(ExprPtr left, ExprPtr right, Kind kind) {
			return GetExprManager()->MkBinOp(left, right, kind);
		}

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
		static ExprPtr Eq(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::EQ); }
		static ExprPtr Ne(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::NE); }
		static ExprPtr UGt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::UGT); }
		static ExprPtr UGe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::UGE); }
		static ExprPtr ULt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::ULT); }
		static ExprPtr ULe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::ULE); }
		static ExprPtr SGt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SGT); }
		static ExprPtr SGe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SGE); }
		static ExprPtr SLt(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SLT); }
		static ExprPtr SLe(ExprPtr l, ExprPtr r) { return Apply(l, r, Kind::SLE); }

		template<typename T> ExprPtr C(T val) { return GetExprManager()->MkConst(GetExprManager()->MkIntVal<T>(val)); }
		template<typename T> ExprPtr V(std::string name) { return GetExprManager()->MkVar(name, GetExprManager()->MkIntTy<T>()); }
	}
}

#endif /* __EXPR_MANAGER_HELPER_HPP__ */













