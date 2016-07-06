#ifndef __PATH_CONSTRAINT_HPP__
#define __PATH_CONSTRAINT_HPP__

#include "object.hpp"
#include "expr.hpp"
#include <list>
#include <vector>
//#include "holder.hpp"

namespace solver {
	using PathConstraint = std::vector<solver::SharedExpr>;
	using PathConstraintPtr = std::shared_ptr<PathConstraint>;
}

#endif













