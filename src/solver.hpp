#ifndef __SOLVER_HPP__
#define __SOLVER_HPP__

#include <memory>
#include <cassert>

#include <cvc4/cvc4.h>

#include "creatable.hpp"
#include "path-constraint.hpp"
#include "holder.hpp"
#include "object.hpp"
#include "expr.hpp"
#include "meta-kind.hpp"

namespace solver {
	class Solver;

	//using SolverPtr = std::shared_ptr<Solver>;
	using SolverRef = Solver&;
	using Kind = CVC4::Kind;
	using Result = CVC4::Result;

	class Solver {
	public:
		NONCOPYABLE(Solver);
		Solver();
		~Solver();
		//CVC4::ExprManager& ExprManager();
		//CVC4::SmtEngine& SmtEngine();
		//CVC4::SymbolTable& SymbolTable();
		//static SolverPtr Create();
		// TODO: refactoring - replace HolderPtr by SharedExpr
		void Constraint(SharedExpr constraint);
		bool IsSat();
		interpreter::MetaInt GetValue(SharedExpr e);
		Type MkBitVectorType(unsigned size);
		Type MkBooleanType();
		SharedExpr MkConst(BitVec val);
		SharedExpr MkConst(bool val);
		SharedExpr MkConversion(utils::MetaKind kind, unsigned new_width, SharedExpr target);
		SharedExpr MkVar(Type type);
		SharedExpr MkExpr(Kind kind, SharedExpr left, SharedExpr right);
		SharedExpr MkExpr(Kind kind, SharedExpr child1, SharedExpr child2, SharedExpr child3);
		//TODO: refactoring:
		void Print();
	private:
		SharedExpr MkConversion__helper(utils::MetaKind kind, unsigned arg);

		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
		PathConstraint path_constraint_;
	};
}

#endif














