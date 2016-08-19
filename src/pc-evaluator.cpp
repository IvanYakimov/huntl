#include "pc-evaluator.hpp"

namespace solver {
	using interpreter::SolutionRecordListPtr;
	PathConstraintEval::PathConstraintEval(PathConstraintRef pc, SolutionRecordListPtr var_vals) :
		path_constraint_(pc),
		var_vals_(var_vals) {
		assert (path_constraint_.size() == pc.size() and pc.size() != 0);
		assert (var_vals_ != nullptr and var_vals->size() == var_vals_->size());
	}

	PathConstraintEval::~PathConstraintEval() {

	}

	void PathConstraintEval::operator ()() {

	}

	void PathConstraintEval::InitiateMemoryMap() {

	}
}













