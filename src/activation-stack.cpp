#include "activation-stack.hpp"

namespace memory {
	ActivationStack::ActivationStack() {
	}

	ActivationStack::~ActivationStack() {
		assert(stack_.size() == 0);
	}

	void ActivationStack::Push(memory::ActivationPtr activation) {
		stack_.push(activation);
	}

	void ActivationStack::Pop() {
		assert (stack_.size() > 0);
		stack_.pop();
	}

	memory::ActivationPtr ActivationStack::top() {
		assert (stack_.size() > 0);
		return stack_.top();
	}
}
