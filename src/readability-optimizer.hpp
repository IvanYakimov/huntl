#ifndef __READABILITY_OPTIMIZER_HPP__
#define __READABILITY_OPTIMIZER_HPP__

#include "context.hpp"
#include "solution.hpp"
#include "holder.hpp"
#include "holder-helper.hpp"
#include "solver.hpp"
#include "bigram-model.hpp"

namespace interpreter {
	class ReadabilityOptimizer {
	public:
		ReadabilityOptimizer(ContextRef context, SolutionListPtr arg_sols, SolutionPtr ret_sol);
		~ReadabilityOptimizer();
		void RestrictionPass();
		void ConcretizationPass();
	private:
		ContextRef context_;
		SolutionListPtr arg_sols_;
		SolutionPtr ret_sol_;
		BigramModel bigrammer_;
		void HandleBigram(SolutionPtr first, SolutionPtr second);
		void ConcretizationHelper(SolutionPtr sol);
		void RestrictionHelper(SolutionPtr sol);
		void RestrictionHelperInteger(solver::SharedExpr variable);
		bool TryMakeReadable(const solver::SharedExpr& x);
		bool TryMakeAlphabetic(const solver::SharedExpr& x);
		bool TryApplyConstraint(const solver::SharedExpr& constraint);
};
}

#endif
