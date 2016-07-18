#include "ram.hpp"

namespace memory {
	Ram::Ram() : stack_() {

	}

	Ram::~Ram() {

	}

	StackRef Ram::Stack() {
		return stack_;
	}
}
