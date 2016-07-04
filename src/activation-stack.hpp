#ifndef __ACTIVATION_STACK_HPP__
#define __ACTIVATION_STACK_HPP__

#include <stack>

#include "activation.hpp"

namespace memory {
	class ActivationStack {
	public:
		void operator++();
		void operator--();
		memory::ActivationPtr activation();
	private:
		std::stack<memory::ActivationPtr> stack_;
	};
}

#endif
