#ifndef __HOLDER_HELPER_HPP__
#define __HOLDER_HELPER_HPP__

#include "solver.hpp"
#include "holder.hpp"
#include "meta-int.hpp"

namespace interpreter {
	interpreter::MetaInt Concretize(solver::SolverRef solver, memory::HolderPtr holder);
}

#endif
