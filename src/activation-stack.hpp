#ifndef __ACTIVATION_STACK_HPP__
#define __ACTIVATION_STACK_HPP__

#include <stack>

#include "activation.hpp"

namespace memory {
	class ActivationStack {
	public:
		ActivationStack();
		~ActivationStack();
		void Push(memory::ActivationPtr activation);
		void Pop();
		memory::ActivationPtr top();
	private:
		std::stack<memory::ActivationPtr> stack_;
	};
}

#endif
