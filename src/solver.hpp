#ifndef __SOLVER_HPP__
#define __SOLVER_HPP__

#include <memory>
#include <cassert>

#include <cvc4/cvc4.h>

#include "creatable.hpp"
#include "path-constraint.hpp"
#include "holder.hpp"
#include "object.hpp"

namespace solver {
	class Solver;

	using SolverPtr = std::shared_ptr<Solver>;

	class Solver {
	public:
		Solver();
		~Solver();
		CVC4::ExprManager& ExprManager();
		CVC4::SmtEngine& SmtEngine();
		CVC4::SymbolTable& SymbolTable();
		static SolverPtr Create();
		void Constraint(memory::HolderPtr holder);
		bool CheckSat();
		void ProduceModel();
		interpreter::BitVec GetValue(memory::HolderPtr holder);
	private:
		CVC4::ExprManager expr_manager_;
		CVC4::SmtEngine smt_engine_;
		CVC4::SymbolTable symbol_table_;
		PathConstraintPtr path_constraint_;
	};
}

#endif














