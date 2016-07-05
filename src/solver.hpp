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

namespace solver {
	class Solver;

	using SolverPtr = std::shared_ptr<Solver>;
	using SolverRef = Solver&;
	using Kind = CVC4::Kind;

	class Solver {
	public:
		NONCOPYABLE(Solver);
		Solver();
		~Solver();
		CVC4::ExprManager& ExprManager();
		CVC4::SmtEngine& SmtEngine();
		CVC4::SymbolTable& SymbolTable();
		static SolverPtr Create();
		// TODO: refactoring - replace HolderPtr by SharedExpr
		void Constraint(memory::HolderPtr holder);
		bool CheckSat();
		memory::HolderPtr GetValue(memory::HolderPtr holder);
		Type MkBitVectorType(unsigned size);
		SharedExpr MkConst(BitVec val);
		SharedExpr MkVar(Type type);
		SharedExpr MkExpr(Kind kind, SharedExpr left, SharedExpr right);
		//TODO: refactoring:
		void Print();
	private:
		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
		PathConstraint path_constraint_;
	};
}

#endif














