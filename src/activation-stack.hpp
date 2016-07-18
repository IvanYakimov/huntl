#ifndef __ACTIVATION_STACK_HPP__
#define __ACTIVATION_STACK_HPP__

#include <stack>

#include "activation.hpp"
#include "ram.hpp"

namespace memory {
	class ActivationStack {
	public:
		ActivationStack(RamRef ram);
		~ActivationStack();
		void Push();
		void Pop();
		memory::ActivationPtr top();
	private:
		std::stack<memory::ActivationPtr> stack_;
		RamRef ram_;
	};
}

#endif
