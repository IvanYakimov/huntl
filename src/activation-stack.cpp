#include "activation-stack.hpp"

namespace memory {
	void ActivationStack::operator++() {
		auto activation = memory::Activation::Create();
		stack_.push(activation);
	}

	void ActivationStack::operator--() {
		assert (stack_.size() > 0);
		stack_.pop();
	}

	memory::ActivationPtr ActivationStack::activation() {
		assert (stack_.size() > 0);
		return stack_.top();
	}
}
