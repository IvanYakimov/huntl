#ifndef __PC_EVALUATOR_HPP__
#define __PC_EVALUATOR_HPP__

#include "path-constraint.hpp"
#include "expr.hpp"
#include "meta-int.hpp"
#include "solution-record.hpp"

#include <map>

namespace solver {
	class PathConstraintEval {
	public:
		PathConstraintEval(PathConstraintRef pc, interpreter::SolutionRecordListPtr var_vals);
		~PathConstraintEval();
		void operator()();
	private:
		PathConstraintRef path_constraint_;
		interpreter::SolutionRecordListPtr var_vals_;
		std::map<SharedExpr, interpreter::MetaInt> memory_map_;
		void InitiateMemoryMap();
	};
}

#endif













