#ifndef __CONTEXT_HPP__
#define __CONTEXT_HPP__

#include "activation-stack.hpp"
#include "solver.hpp"

namespace interpreter {
	struct Context {
		memory::ActivationStack activation_stack;
		solver::Solver solver;
	};
}

#endif
