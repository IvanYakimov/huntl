#include "context.hpp"

namespace interpreter {
	using memory::RamRef;

	Context::Context() : solver_(), ram_(), activation_stack_(ram_) {
	}

	Context::~Context() {

	}

	solver::SolverRef Context::Solver() {
		return solver_;
	}

	memory::ActivationPtr Context::Top() {
		return activation_stack_.top();
	}

	void Context::Push() {
		//auto new_activation = memory::Activation::Create();
		activation_stack_.Push();
	}

	RamRef Context::Ram() {
		return (RamRef)ram_;
	}

	/*
	void Context::Push(memory::ActivationPtr activation) {
		activation_stack.Push(activation);
	}
	*/

	void Context::Pop() {
		activation_stack_.Pop();
	}
}















