#include "activation-stack.hpp"

namespace memory {
	ActivationStack::ActivationStack(RamRef ram) : ram_(ram) {
	}

	ActivationStack::~ActivationStack() {
		assert(stack_.size() == 0);
	}

	void ActivationStack::Push() {
		memory::ActivationPtr activation = Activation::Create(ram_);
		stack_.push(activation);
		ram_.Stack().Push();
	}

	void ActivationStack::Pop() {
		assert (stack_.size() > 0);
		stack_.pop();
		ram_.Stack().Pop();
	}

	memory::ActivationPtr ActivationStack::top() {
		assert (stack_.size() > 0);
		return stack_.top();
	}
}
