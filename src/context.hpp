#ifndef __CONTEXT_HPP__
#define __CONTEXT_HPP__

#include "activation-stack.hpp"
#include "solver.hpp"
#include "object.hpp"
#include "memory-map-interface.hpp"

namespace interpreter {
	struct Context;

	//using ContextPtr = std::shared_ptr<Context>;
	using ContextRef = Context&;

	class Context {
	public:
		Context();
		~Context();
		NONCOPYABLE(Context);
		solver::SolverRef Solver();
		//void Push(memory::ActivationPtr activation);
		void Push();
		void Pop();
		memory::ActivationPtr Top();
	private:
		memory::ActivationStack activation_stack;
		solver::Solver solver_;
	};
}

#endif
















