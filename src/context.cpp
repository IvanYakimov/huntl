#include "context.hpp"

namespace interpreter {
	Context::Context() {
	}

	Context::~Context() {

	}

	solver::SolverRef Context::Solver() {
		return solver_;
	}

	memory::ActivationPtr Context::Top() {
		return activation_stack.top();
	}

	void Context::Push(memory::ActivationPtr activation) {
		activation_stack.Push(activation);
	}

	void Context::Pop() {
		activation_stack.Pop();
	}
}














